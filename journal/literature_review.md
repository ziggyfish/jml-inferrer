# Literature Review: Specification Inference, JML Verification, and Spec-Driven Bug Detection

Compiled 2026-04-30 from a five-agent parallel sweep of the literature relevant to the JML Inferrer PhD project. The review covers (1) the JML and Java verification ecosystem, (2) static and dynamic specification inference, (3) loop-invariant inference specifically, (4) LLM-driven specification synthesis, and (5) specification-based test generation and spec-driven bug detection.

The narrative through-line: a heuristic AST-based JML inference tool downstream-verified by OpenJML occupies a sparsely populated niche. The two closest classical comparators are **Houdini** (template + verifier filtering, JML/ESC) and **DynaMate** (postcondition-mutation, JML, requires user postcondition). The most direct contemporary comparator is **SpecGen** (LLM-driven JML synthesis with verifier feedback). Almost everything else lives in a different language ecosystem (C/ACSL, Dafny, Boogie, Solidity) or a different output format (FSMs, separation logic).

---

## Contents

1. Executive summary and positioning
2. Foundations: JML, the contract idiom, and verifier infrastructure
3. Specification inference and mining
4. Loop-invariant inference (deep dive)
5. LLM-driven specification synthesis (2023–2026)
6. NL-driven specification inference
7. Specification-based test generation
8. Spec-driven bug detection (the thesis line)
9. Surveys, retrospectives, and benchmarks
10. Where the JML Inferrer fits
11. Open problems and gaps the JML Inferrer addresses

---

## 1. Executive summary and positioning

### 1.1 The four methodological axes

Specification-inference work splits cleanly along four axes:

| Axis | Endpoints |
|---|---|
| **Source of evidence** | Static (AST/IR) ↔ Dynamic (traces) ↔ Symbolic (path conditions) ↔ Neural (LLM/NN) |
| **Search style** | Templates (fixed grammar) ↔ Fixpoint (abstract interpretation) ↔ Learning (decision tree / NN / LLM) ↔ Heuristic AST (this work) |
| **Soundness gate** | Sound by construction (abstract interpretation, ICE) ↔ Verifier-filtered (Houdini, SpecGen) ↔ Statistical (Daikon) ↔ Unverified (raw LLM) |
| **Output format** | Pre/postconditions ↔ Loop invariants ↔ Class/type invariants ↔ Frame conditions ↔ FSAs / temporal properties |

The JML Inferrer is **Static / Heuristic AST / Verifier-filtered (downstream) / Pre+Post+Loop+Class+Frame**. The point in this design space that is most populated is *Dynamic / Templates / Statistical* (Daikon and successors); the points most populated for loop invariants specifically are *Static / Templates+Constraints / Sound* (Cousot–Halbwachs polyhedra, ICE-DT, LoopInvGen) and increasingly *Neural / Verifier-filtered* (Code2Inv, CLN2INV, Lemur, Loopy). Pure heuristic AST is uncommon and its closest precedent is Furia & Meyer 2010's postcondition-mutation rules.

### 1.2 Direct competitors at the JML/Java boundary

Five works occupy the same niche (Java code → JML or JML-like specs, downstream-verified):

| Work | Year | Method | Status |
|---|---|---|---|
| **Houdini** | 2001 | Template + ESC/Java filtering | Abandoned |
| **Daikon (Java front-end)** | 2001/2007 | Dynamic, template-based | Active |
| **DynaMate** | 2014/2015 | Postcondition mutation + dynamic + ESC/Java2 | Inactive |
| **EvoSpex** | 2021 | Evolutionary postcondition learning | Active |
| **SpecGen** | 2024/2025 | LLM + mutation + OpenJML | Active |

These five are the **must-cite** competitors for any JML-Inferrer paper.

### 1.3 The gap the JML Inferrer fills

There is no continuously maintained tool that takes raw Java source, emits JML preconditions + postconditions + loop invariants + class invariants + frame conditions in tandem, and is downstream-verified by OpenJML. Houdini's template/verifier loop is the conceptual ancestor; DynaMate covers loop invariants but assumes user postconditions; SpecGen is the LLM-based alternative the user has explicitly deferred. The JML Inferrer occupies the heuristic AST point of the design space without a current rival.

---

## 2. Foundations: JML, the contract idiom, and verifier infrastructure

### 2.1 The JML language

**Leavens, Baker & Ruby (2006).** Preliminary design of JML: a behavioral interface specification language for Java. *ACM SIGSOFT Software Engineering Notes*, 31(3), 1–38. DOI: 10.1145/1127878.1127884. Originally Iowa State Tech Report 98-06. — *The foundational JML paper. Defines JML as a behavioral interface specification language (BISL) blending Eiffel-style executable Java assertions with Larch-style model-based abstraction. Establishes pre/postconditions, invariants, and ghost/model variables.*

**Leavens, Cheon, Clifton, Ruby & Cok (2005).** How the design of JML accommodates both runtime assertion checking and formal verification. *Science of Computer Programming*, 55(1–3), 185–208. — *Articulates the dual-use design tension between RAC and ESC.*

**Jacobs & Poll (2001).** A logic for the Java Modeling Language JML. *FASE 2001*, LNCS 2029, 284–299. DOI: 10.1007/3-540-45314-8_21. — *Hoare-style semantics for JML, including normal/exceptional postconditions.*

**Leavens et al. (2007).** Tutorial on JML, the Java Modeling Language. *ASE 2007*, 573. DOI: 10.1145/1321631.1321747.

**Burdy, Cheon, Cok, Ernst, Kiniry, Leavens, Leino & Poll (2005).** An overview of JML tools and applications. *International Journal on Software Tools for Technology Transfer*, 7(3), 212–232. DOI: 10.1007/s10009-004-0167-4. — *The canonical JML ecosystem survey, organising the verification, RAC, test, and documentation tools and their interplay. Mandatory citation.*

### 2.2 JML-targeted static verifiers

**Flanagan, Leino, Lillibridge, Nelson, Saxe & Stata (2002).** Extended Static Checking for Java. *PLDI 2002*, 234–245. DOI: 10.1145/512529.512558. — *Compaq SRC's ESC/Java; the direct ancestor of OpenJML.*

**Cok & Kiniry (2005).** ESC/Java2: Uniting ESC/Java and JML. *CASSIS 2004*, LNCS 3362, 108–128. DOI: 10.1007/978-3-540-30569-9_6.

**Cok (2011).** OpenJML: JML for Java 7 by Extending OpenJDK. *NFM 2011*, LNCS 6617, 472–479. DOI: 10.1007/978-3-642-20398-5_35. — **The verification target for the JML Inferrer.**

**Cok (2014).** OpenJML: Software verification for Java 7 using JML, OpenJDK, and Eclipse. *F-IDE 2014*, EPTCS 149, 79–92. arXiv:1404.6608. — *Documents the SMT interface (CVC4 and Z3) and VCG.*

**Cok (2021).** JML and OpenJML for Java 16. *FTfJP 2021*, 65–67. DOI: 10.1145/3464971.3468417. — *Most recent OpenJML paper; documents support for modules, sealed classes, switch expressions, records, pattern matching.*

**Ahrendt, Beckert, Bubel, Hähnle, Schmitt & Ulbrich (eds.) (2016).** Deductive Software Verification — The KeY Book. LNCS 10001. Springer. DOI: 10.1007/978-3-319-49812-6. — *Definitive reference on KeY, the leading interactive JML verifier; chapter on JML included.*

**Boerman, Huisman & Joosten (2018).** Reasoning About JML: Differences Between KeY and OpenJML. *iFM 2018*, LNCS 11023, 30–46. DOI: 10.1007/978-3-319-98938-9_3. — *Side-by-side comparison; identifies semantic divergences. Cite when arguing for portability between back-ends.*

**Marché, Paulin-Mohring & Urbain (2004).** The Krakatoa tool for certification of Java/JavaCard programs annotated in JML. *Journal of Logic and Algebraic Programming*, 58(1–2), 89–106. DOI: 10.1016/j.jlap.2003.07.006.

**Burdy, Requet & Lanet (2003); Barthe, Burdy, Charles, Grégoire, Huisman, Lanet, Pavlova & Requet (2007).** JACK — A Tool for Validation of Security and Behaviour of Java Applications. *FME 2003*, LNCS 2805, 422–439; *FMCO 2006*, LNCS 4709, 152–174. — *Smart-card-targeted JML verifier; abandoned post-Gemalto.*

### 2.3 JML runtime and test infrastructure

**Cheon (2003).** A Runtime Assertion Checker for the Java Modeling Language. PhD thesis, Iowa State University, TR 03-09. — *The original `jmlc` runtime checker.*

**Cheon & Leavens (2002).** A simple and practical approach to unit testing: The JML and JUnit way. *ECOOP 2002*, LNCS 2374, 231–255. DOI: 10.1007/3-540-47993-7_10. — *AITO Test of Time Award 2022.*

**Zimmerman & Nagmoti (2010).** JMLUnit: The Next Generation. *FoVeOOS 2010*, LNCS 6528, 183–197. DOI: 10.1007/978-3-642-18070-5_13. — *TestNG-based, Java 1.5+ generics. Active.*

**Lehner & Müller (2008).** JML Runtime Assertion Checking: Improved Error Reporting and Efficiency Using Strong Validity. *FM 2008*, LNCS 5014, 285–300. DOI: 10.1007/978-3-540-68237-0_18.

### 2.4 Adjacent Java verification platforms (non-JML)

**Jacobs, Smans, Philippaerts, Vogels, Penninckx & Piessens (2011).** VeriFast: A Powerful, Sound, Predictable, Fast Verifier for C and Java. *NFM 2011*, LNCS 6617, 41–55. DOI: 10.1007/978-3-642-20398-5_4. — *Separation-logic-based.*

**Cordeiro, Kesseli, Kroening, Schrammel & Trtik (2018).** JBMC: A Bounded Model Checking Tool for Verifying Java Bytecode. *CAV 2018*, LNCS 10981, 183–190. DOI: 10.1007/978-3-319-96145-3_10. — *Bytecode BMC; bug-finding companion to deductive verification.*

**Beckert, Kirsten, Klamroth & Ulbrich (2020).** Modular Verification of JML Contracts Using Bounded Model Checking. *ISoLA 2020*, LNCS 12477, 60–80. DOI: 10.1007/978-3-030-61362-4_4. — *JJBMC; specs the JML Inferrer emits could in principle be discharged here too.*

**Kahsai, Rümmer, Sanchez & Schäf (2016).** JayHorn: A Framework for Verifying Java Programs. *CAV 2016*, LNCS 9779, 352–358. DOI: 10.1007/978-3-319-41528-4_19. — *Translates Java to Constrained Horn Clauses.*

**Robby, Hatcliff & Belt (2024).** Logika: The Sireum Verification Framework. *FMICS 2024*, LNCS 14952, 96–115. DOI: 10.1007/978-3-031-68150-9_6.

**Visser, Havelund, Brat, Park & Lerda (2003).** Model Checking Programs. *Automated Software Engineering*, 10(2), 203–232. DOI: 10.1023/A:1022920129859. — *Java PathFinder.*

**Pasareanu, Visser, Bushnell, Geldenhuys, Mehlitz & Rungta (2013).** Symbolic PathFinder: Integrating Symbolic Execution with Model Checking for Java Bytecode Analysis. *Automated Software Engineering*, 20(3), 391–425. DOI: 10.1007/s10515-013-0122-2.

**Braione, Denaro & Pezzè (2016).** JBSE: A Symbolic Executor for Java Programs with Complex Heap Inputs. *FSE 2016 Tool Demos*, 1018–1022. DOI: 10.1145/2950290.2983940.

### 2.5 Adjacent contract languages

**Meyer (1992, 1997).** Applying "Design by Contract." *IEEE Computer*, 25(10), 40–51; *Object-Oriented Software Construction* (2nd ed.), Prentice Hall. — *Eiffel; the conceptual ancestor of JML.*

**Guttag, Horning & Wing (1985, 1993).** The Larch family of specification languages. *IEEE Software*, 2(5), 24–36; book ISBN 0-387-94006-5. — *The other principal ancestor of JML.*

**Barnett, Leino & Schulte (2005).** The Spec# programming system: An overview. *CASSIS 2004*, LNCS 3362, 49–69. DOI: 10.1007/978-3-540-30569-9_3. — *C# extended with non-null types and contracts. Project closed.*

**Barnett, Fähndrich, Leino, Müller, Schulte & Venter (2011).** Specification and verification: The Spec# experience. *CACM*, 54(6), 81–91. DOI: 10.1145/1953122.1953131.

**Leino (2010).** Dafny: An Automatic Program Verifier for Functional Correctness. *LPAR-16*, LNCS 6355, 348–370. DOI: 10.1007/978-3-642-17511-4_20. — *Verification-aware language; loop invariants are user-required.*

**Baudin, Cuoq, Filliâtre, Marché et al. (2008–current).** ACSL: ANSI/ISO C Specification Language. CEA-LIST and Inria, Frama-C documentation.

**Kirchner, Kosmatov, Prevosto, Signoles & Yakobowski (2015).** Frama-C: A software analysis perspective. *Formal Aspects of Computing*, 27(3), 573–609. DOI: 10.1007/s00165-014-0326-7.

**Filliâtre & Paskevich (2013).** Why3 — Where Programs Meet Provers. *ESOP 2013*, LNCS 7792, 125–128. DOI: 10.1007/978-3-642-37036-6_8.

### 2.6 SMT and the underlying solver layer

**de Moura & Bjørner (2008).** Z3: An Efficient SMT Solver. *TACAS 2008*, LNCS 4963, 337–340. DOI: 10.1007/978-3-540-78800-3_24. — *The default OpenJML back-end.*

**Barbosa et al. (2022).** cvc5: A Versatile and Industrial-Strength SMT Solver. *TACAS 2022*, LNCS 13243, 415–442. DOI: 10.1007/978-3-030-99524-9_24.

**Conchon, Coquereau, Iguernlala & Mebsout (2018).** Alt-Ergo 2.2. *SMT Workshop 2018*. — *Used in Why3 / SPARK.*

**Barnett, Chang, DeLine, Jacobs & Leino (2005).** Boogie: A Modular Reusable Verifier for Object-Oriented Programs. *FMCO 2005*, LNCS 4111, 364–387. DOI: 10.1007/11804192_17. — *VC-generation IL underlying Spec#, Dafny, VCC.*

### 2.7 Theoretical foundations

**Cousot & Cousot (1977).** Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints. *POPL 1977*, 238–252. DOI: 10.1145/512950.512973. — *Foundational framework.*

**Cousot & Cousot (1992).** Comparing the Galois connection and widening/narrowing approaches to abstract interpretation. *PLILP 1992*, LNCS 631, 269–295. — *Widening/narrowing.*

**Karr (1976).** Affine relationships among variables of a program. *Acta Informatica*, 6, 133–151. DOI: 10.1007/BF00268497.

**Cousot & Halbwachs (1978).** Automatic discovery of linear restraints among variables of a program. *POPL 1978*, 84–96. DOI: 10.1145/512760.512770. — *Polyhedral domain.*

**Miné (2006).** The octagon abstract domain. *Higher-Order and Symbolic Computation*, 19(1), 31–100. DOI: 10.1007/s10990-006-8609-1.

---

## 3. Specification inference and mining

### 3.1 Static inference: the Houdini family

**Flanagan & Leino (2001).** Houdini, an Annotation Assistant for ESC/Java. *FME 2001*, LNCS 2021, 500–517. DOI: 10.1007/3-540-45251-6_29. — **The canonical JML inference tool and the closest classical competitor.** Generates a large pool of candidate annotations (null, range, field invariants), then iterates ESC/Java to discard the unprovable ones (greatest-fixpoint). Sound (every retained annotation is verifier-checked) but limited to the candidate template grammar. Companion: Flanagan, Joshi & Leino (2001), *Annotation inference for modular checkers*, Information Processing Letters 77(2–4), 97–108.

**Lahiri & Vanegue (2011).** ExplainHoudini: Making Houdini Inference Transparent. *VMCAI 2011*, LNCS 6538, 72–87. DOI: 10.1007/978-3-642-18275-4_22. — *Diagnostic refinement explaining why a Houdini candidate was dropped.*

### 3.2 Static inference: abstract-interpretation-based

**Fähndrich & Logozzo (2010).** Static Contract Checking with Abstract Interpretation. *FoVeOOS 2010*, LNCS 6528, 10–30. DOI: 10.1007/978-3-642-18070-5_2. — *Clousot / Microsoft CodeContracts; intervals, octagons, polyhedra, parametric array segmentation.*

**Cousot, Cousot, Logozzo & Barnett (2013).** An Abstract Interpretation Framework for Refactoring with Application to Extract Methods with Contracts. *OOPSLA 2013*, 213–232.

**Cousot, Cousot & Logozzo (2011).** Precondition Inference from Intermittent Assertions and Application to Contracts on Collections. *VMCAI 2011*, LNCS 6538, 150–168. DOI: 10.1007/978-3-642-18275-4_12.

**Cousot, Cousot & Logozzo (2013).** Automatic Inference of Necessary Preconditions. *VMCAI 2013*, LNCS 7737, 128–148. — *Theoretical justification for "if a branch throws, requires the negation".*

**Logozzo & Ball (2012).** Inference of Necessary Field Conditions with Abstract Interpretation. *OOPSLA 2012*, 173–190. DOI: 10.1145/2384616.2384651. — *Class-invariant inference.*

### 3.3 Dynamic inference: the Daikon family

**Ernst, Cockrell, Griswold & Notkin (2001).** Dynamically Discovering Likely Program Invariants to Support Program Evolution. *IEEE Transactions on Software Engineering*, 27(2), 99–123. DOI: 10.1109/32.908957.

**Ernst, Perkins, Guo, McCamant, Pacheco, Tschantz & Xiao (2007).** The Daikon system for dynamic detection of likely invariants. *Science of Computer Programming*, 69(1–3), 35–45. DOI: 10.1016/j.scico.2007.01.015. — **The dominant baseline.** Outputs JML, ESC/Java, Eiffel-style assertions. Templates include `x ≥ 0`, `x = y`, `array a is sorted`, `for all elements e: e.field > 0`. Limitations: dependence on test-suite coverage, limited expressiveness on quantified facts.

**Hangal & Lam (2002).** Tracking Down Software Bugs Using Automatic Anomaly Detection. *ICSE 2002*, 291–301. DOI: 10.1145/581339.581377. — *DIDUCE; bytecode-instrumenting Java tool. Online range/bit-mask invariants.*

**Csallner, Tillmann & Smaragdakis (2008).** DySy: Dynamic Symbolic Execution for Invariant Inference. *ICSE 2008*, 281–290. DOI: 10.1145/1368088.1368127. — *Combines concrete with concolic execution; path conditions become invariants. .NET/Pex.*

**Polikarpova, Ciupa & Meyer (2009).** A Comparative Study of Programmer-Written and Automatically Inferred Contracts. *ISSTA 2009*, 93–104. DOI: 10.1145/1572272.1572285. — *Citadel (Daikon-for-Eiffel). Establishes the recall-against-human, precision-via-verifier evaluation protocol.*

**Nguyen, Kapur, Weimer & Forrest (2014).** DIG: A dynamic invariant generator for polynomial and array invariants. *ACM TOSEM*, 23(4), Article 30. DOI: 10.1145/2556782.

**Nguyen, Dwyer & Visser (2017).** SymInfer: Inferring Program Invariants Using Symbolic States. *ASE 2017*, 804–814. — *Symbolic-execution-driven invariant generation.*

**Le, Sun & Nguyen (2019).** SLING: Using dynamic analysis to infer program invariants in separation logic. *PLDI 2019*, 1185–1199. — *Heap-shape predicates.*

### 3.4 Hybrid: postcondition mutation + dynamic + static

**Furia & Meyer (2010).** Inferring Loop Invariants Using Postconditions. *Fields of Logic and Computation*, LNCS 6300, 277–300. DOI: 10.1007/978-3-642-15025-8_15. — **Direct conceptual ancestor of the JML Inferrer's loop-invariant heuristics.** Catalogue of mutation rules (uncoupling, constant relaxation, variable introduction).

**Galeotti, Furia, May, Fraser & Zeller (2014, 2015).** DynaMate: Dynamically Inferring Loop Invariants for Automatic Full Functional Verification. *HVC 2014*, LNCS 8855, 48–53; *IEEE TSE*, 41(10), 1019–1037. DOI: 10.1109/TSE.2015.2422707. — **Closest precedent in the JML ecosystem.** Mutates user-supplied postcondition, runs tests on each candidate, calls ESC/Java2 to retain provable ones. 97% obligations discharged on 26 java.util methods.

### 3.5 Frame-condition inference

**Kogtenkov, Meyer & Velder (2015).** Alias calculus, change calculus and frame inference. *Science of Computer Programming*, 97, 163–172. DOI: 10.1016/j.scico.2013.11.006. — *Recovers `modify`/`assignable` clauses from the postcondition's set of changed expressions. Eiffel; principle generalises to JML.*

**Calcagno, Distefano, O'Hearn & Yang (2009, 2011).** Compositional Shape Analysis by Means of Bi-Abduction. *POPL 2009*, 289–300; *JACM* 58(6), Article 26. — *Industrial-scale separation-logic spec inference (Facebook Infer).*

### 3.6 Constraint-based and template-based methods

**Colón, Sankaranarayanan & Sipma (2003).** Linear invariant generation using non-linear constraint solving. *CAV 2003*, LNCS 2725, 420–432. DOI: 10.1007/978-3-540-45069-6_39.

**Sankaranarayanan, Sipma & Manna (2004).** Constraint-based linear-relations analysis. *SAS 2004*, LNCS 3148, 53–68.

**Sankaranarayanan, Sipma & Manna (2004).** Non-linear loop invariant generation using Gröbner bases. *POPL 2004*, 318–329. DOI: 10.1145/964001.964028.

**Gupta & Rybalchenko (2009).** InvGen: An efficient invariant generator. *CAV 2009*, LNCS 5643, 634–640. DOI: 10.1007/978-3-642-02658-4_48. — *Linear-arithmetic invariant generator with dynamic seeding.*

**Srivastava & Gulwani (2009).** Program verification using templates over predicate abstraction. *PLDI 2009*, 223–234.

### 3.7 Specification mining (FSMs and temporal patterns)

**Ammons, Bodík & Larus (2002).** Mining Specifications. *POPL 2002*, 4–16. DOI: 10.1145/503272.503275. — *Coined "specification mining"; learns probabilistic FSAs from execution traces.*

**Engler, Chen, Hallem, Chou & Chelf (2001).** Bugs as Deviant Behavior: A General Approach to Inferring Errors in Systems Code. *SOSP 2001*, 57–72. DOI: 10.1145/502034.502041. — **Foundational for "inferred specs find real bugs".**

**Li & Zhou (2005).** PR-Miner: Automatically Extracting Implicit Programming Rules and Detecting Violations. *ESEC/FSE 2005*, 306–315. DOI: 10.1145/1081706.1081755.

**Henkel & Diwan (2003).** Discovering Algebraic Specifications from Java Classes. *ECOOP 2003*, LNCS 2743, 431–456. DOI: 10.1007/978-3-540-45070-2_19.

**Yang, Evans, Bhardwaj, Bhat & Das (2006).** Perracotta: Mining Temporal API Rules from Imperfect Traces. *ICSE 2006*, 282–291. DOI: 10.1145/1134285.1134325.

**Le Goues & Weimer (2009).** Specification Mining with Few False Positives. *TACAS 2009*, LNCS 5505, 509–524. DOI: 10.1007/978-3-642-00768-2_38.

**Lorenzoli, Mariani & Pezzè (2008).** Automatic Generation of Software Behavioral Models. *ICSE 2008*, 501–510. DOI: 10.1145/1368088.1368157. — *GK-tail; FSMs with data-value predicates.*

**Beschastnikh, Brun, Schneider, Sloan & Ernst (2011).** Leveraging Existing Instrumentation to Automatically Infer Invariant-Constrained Models. *ESEC/FSE 2011*, 267–277. DOI: 10.1145/2025113.2025151. — *Synoptic.*

**Lemieux, Park & Beschastnikh (2015).** General LTL Specification Mining. *ASE 2015*, 81–92. DOI: 10.1109/ASE.2015.71. — *Texada.*

**Beschastnikh, Brun, Abrahamson, Ernst & Krishnamurthy (2013, 2015).** Unifying FSM-Inference Algorithms through Declarative Specification. *ICSE 2013*, 252–261; *IEEE TSE* 41(4), 408–421. — *InvariMint.*

**Le & Lo (2021).** Adversarial Specification Mining. *ACM TOSEM*, 30(2), Article 16. DOI: 10.1145/3424307. — *DICE-Tester / DICE-Miner.*

**Vasudevan, Sheridan, Patel, Tcheng, Tuohy & Johnson (2010, 2014).** GoldMine: Automatic Assertion Generation Using Data Mining and Static Analysis. *DATE 2010*, 626–629; *IEEE TCAD* 33(3), 405–418. — *Hardware analogue of Houdini.*

**Robillard, Bodden, Kawrykow, Mezini & Ratchford (2013).** Automated API Property Inference Techniques. *IEEE TSE*, 39(5), 613–637. DOI: 10.1109/TSE.2012.63. — **Required citation for any specification-inference review.**

**Lo, Khoo, Han & Liu (eds.) (2011).** Mining Software Specifications: Methodologies and Applications. Chapman & Hall/CRC. ISBN 978-1439806265.

### 3.8 Search-based and evolutionary

**Molina, Ponzio, Aguirre & Frias (2021).** EvoSpex: An Evolutionary Algorithm for Learning Postconditions. *ICSE 2021*, 1223–1235. DOI: 10.1109/ICSE43902.2021.00112. — **Direct competitor.** GA over JML-like assertion grammar; dynamic-trace-supervised.

**Terragni, Jahangirova, Tonella & Pezzè (2020, 2021).** Evolutionary Improvement of Assertion Oracles. *ESEC/FSE 2020*, 1178–1189; arXiv:2103.02901. — *GAssert.*

### 3.9 Symbolic-execution-driven

**Pasareanu & Visser (2004).** Verification of Java Programs Using Symbolic Execution and Invariant Generation. *SPIN 2004*, LNCS 2989, 164–181. DOI: 10.1007/978-3-540-24732-6_13. — *Predicate-abstraction-based class-invariant inference inside JPF.*

---

## 4. Loop-invariant inference (deep dive)

### 4.1 Abstract interpretation

Foundations: Cousot & Cousot 1977, Karr 1976, Cousot & Halbwachs 1978, Miné 2006 (covered in §2.7).

**Jeannet & Miné (2009).** Apron: A library of numerical abstract domains for static analysis. *CAV 2009*, LNCS 5643, 661–667. — *Reusable numerical-AI library; standard substrate for academic and production analysers.*

**Cousot, Cousot, Feret, Mauborgne, Miné, Monniaux & Rival (2007).** Combination of abstractions in the ASTRÉE static analyzer. *ASIAN 2006*, LNCS 4435, 272–300. — *Industrial-strength multi-domain analyser. Verified Airbus A340/A380 flight-control software with zero false alarms.*

**Brat, Navas, Shi & Venet (2014).** IKOS: A framework for static analysis based on abstract interpretation. *SEFM 2014*, LNCS 8702, 271–277. DOI: 10.1007/978-3-319-10431-7_20.

**Bühler, Cuoq, Yakobowski, Lemerre, Maroneze, Perelle & Prevosto (2017).** EVA, an Evolved Value Analysis for Frama-C. — *The closest spiritual analogue in the C/ACSL world. EVA is fixpoint-based and sound; the JML Inferrer is heuristic and unsound (with OpenJML providing the soundness gate).*

### 4.2 Predicate abstraction and software model checking

**Ball & Rajamani (2001).** The SLAM toolkit. *CAV 2001*, LNCS 2102, 260–264. — *Microsoft's Static Driver Verifier.*

**Ball, Levin & Rajamani (2011).** A decade of software model checking with SLAM. *CACM*, 54(7), 68–76. DOI: 10.1145/1965724.1965743. — *270 confirmed bugs in 140 device drivers.*

**Henzinger, Jhala, Majumdar & Sutre (2002).** Lazy abstraction. *POPL 2002*, 58–70. — *BLAST.*

**Henzinger, Jhala, Majumdar & McMillan (2004).** Abstractions from proofs. *POPL 2004*, 232–244. — *Interpolation-based predicate discovery.*

**McMillan (2005).** Applications of Craig interpolation to model checking. *TACAS 2005*, LNCS 3440, 1–12.

**Clarke, Grumberg, Jha, Lu & Veith (2000).** Counterexample-guided abstraction refinement. *CAV 2000*, LNCS 1855, 154–169. *JACM* 50(5), 752–794. — *CEGAR; CAV Award 2015.*

### 4.3 IC3, PDR, and Horn-clause solving

**Bradley (2011).** SAT-based model checking without unrolling. *VMCAI 2011*, LNCS 6538, 70–87. DOI: 10.1007/978-3-642-18275-4_7. — *IC3.*

**Hoder & Bjørner (2012).** Generalized property directed reachability. *SAT 2012*, LNCS 7317, 157–171. — *Theory-aware PDR; Z3 µZ engine.*

**Komuravelli, Gurfinkel & Chaki (2014, 2016).** SMT-based model checking for recursive programs. *FMCAD 2014*; *Formal Methods in System Design* 48(3), 175–205. — *Spacer.*

**Gurfinkel, Kahsai, Komuravelli & Navas (2015).** The SeaHorn verification framework. *CAV 2015*, LNCS 9206, 343–361. DOI: 10.1007/978-3-319-21690-4_20.

### 4.4 Decision-tree, PAC, and CEGIS

**Garg, Löding, Madhusudan & Neider (2014).** ICE: A robust framework for learning invariants. *CAV 2014*, LNCS 8559, 69–87.

**Garg, Neider, Madhusudan & Roth (2016).** Learning invariants using decision trees and implication counterexamples. *POPL 2016*, 499–512. DOI: 10.1145/2837614.2837664. — *ICE-DT.*

**Ezudheen, Neider, D'Souza, Garg & Madhusudan (2018).** Horn-ICE Learning for Synthesizing Invariants and Contracts. *OOPSLA 2018*, 131:1–131:25. DOI: 10.1145/3276501.

**Padhi, Sharma & Millstein (2016).** Data-Driven Precondition Inference with Learned Features. *PLDI 2016*, 42–56. DOI: 10.1145/2908080.2908099. *PIE / LoopInvGen; SyGuS-Comp winner.*

**Krishna, Puhrsch & Wies (2015).** Learning invariants using decision trees. arXiv:1501.04725.

**Sharma & Aiken (2014).** From invariant checking to invariant inference using randomized search. *CAV 2014*, LNCS 8559, 88–105.

### 4.5 Neural

**Si, Dai, Raghothaman, Naik & Song (2018, 2020).** Learning loop invariants for program verification. *NeurIPS 2018*, 7762–7773; *Code2Inv: A Deep Learning Framework for Program Verification*, *CAV 2020*, LNCS 12225, 151–164. — **The prototypical neural inference work.** Solves 106/133 problems vs. 100 for ICE-DT.

**Ryan, Wong, Yao, Gu & Jana (2020).** CLN2INV: Learning Loop Invariants with Continuous Logic Networks. *ICLR 2020*. arXiv:1909.11542. — *Solves all 124 theoretically solvable Code2Inv problems; ~40× faster than Code2Inv.*

**Yao, Ryan, Wong, Jana & Gu (2020).** Learning nonlinear loop invariants with gated continuous logic networks. *PLDI 2020*, 106–120. DOI: 10.1145/3385412.3385986. — *G-CLN; polynomial invariants. Solves 26/27 nonlinear benchmarks.*

**LIPuS (2023).** Loop Invariant Inference through SMT Solving Enhanced Reinforcement Learning. *ISSTA 2023*. DOI: 10.1145/3597926.3598047.

### 4.6 LLM (2023–2026)

**Wu, Barrett & Narodytska (2024).** Lemur: Integrating Large Language Models in Automated Program Verification. *ICLR 2024*. arXiv:2310.04870. — *Sound proof system interleaving LLM proposals (loop invariants/lemmas) with SMT checking. 107/133 Code2Inv with 4.7 LLM calls per instance.*

**Wu, Cao, Yao, Wei, Chen & Ma (2024).** LLM Meets Bounded Model Checking: Neuro-symbolic Loop Invariant Inference. *ASE 2024*. DOI: 10.1145/3691620.3695014. — *LaM4Inv. 309/316 vs 218 best-baseline.*

**Kamath, Senthilnathan, Chakraborty, Deligiannis, Lahiri, Lal, Rastogi, Roy & Sharma (2023).** Finding Inductive Loop Invariants using Large Language Models. arXiv:2311.07948. — *Loopy.*

**Chakraborty, Lahiri, Fakhoury, Musuvathi, Lal, Rastogi, Senthilnathan, Sharma & Swamy (2023).** Ranking LLM-Generated Loop Invariants for Program Verification. *EMNLP Findings 2023*. arXiv:2310.09342. — *iRank; median rank of correct invariant 31 → 4.*

**Wei et al. (2025).** Quokka: Accelerating Program Verification with LLMs via Invariant Synthesis. arXiv:2509.21629.

**Anonymous (2025).** Loop Invariant Generation: A Hybrid Framework of Reasoning Optimised LLMs and SMT Solvers. arXiv:2508.00419. — *o1/o3-mini + SMT; near-100% on Code2Inv, ~1 proposal per problem.*

**Liu et al. (2024, 2025).** ACInv. arXiv:2412.10483; SCP 2025. — *Static analysis + LLM hybrid; 21% over baselines on mixed benchmark.*

**Liu et al. (2025).** LLM For Loop Invariant Generation and Fixing: How Far Are We? arXiv:2511.06552.

**Pei, Bieber, Shi, Sutton & Yin (2023).** Can Large Language Models Reason about Program Invariants? *ICML 2023*. PMLR 202:27496. — *Foundational result; static prediction at quality comparable to Daikon-with-5-traces.*

### 4.7 Algebraic and theorem-prover methods

**Kovács (2008).** Reasoning algebraically about P-solvable loops. *TACAS 2008*, LNCS 4963, 249–264. — *Aligator.*

**Hoder, Kovács & Voronkov (2011).** Invariant Generation in Vampire. *TACAS 2011*, LNCS 6605, 60–64. — *Symbol elimination in a first-order theorem prover.*

### 4.8 Synthesis-based and grammar-based

**Fedyukovich, Kaufman & Bodík (2017, 2020).** Sampling invariants from frequency distributions. *FMCAD 2017*, 100–107; *FMSD* 56. DOI: 10.1007/s10703-020-00349-x. — *FreqHorn. Spiritually closest to the JML Inferrer's pattern-catalogue approach.*

**Fedyukovich, Prabhu, Madhukar & Gupta (2019).** Quantified Invariants via Syntax-Guided Synthesis. *CAV 2019*, LNCS 11561, 259–277. DOI: 10.1007/978-3-030-25540-4_14. — **Direct competitor for `(\forall int k; ...; arr[k] PRED)` emission.**

---

## 5. LLM-driven specification synthesis (2023–2026)

Field is fast-moving; many entries are arXiv preprints. Lean toward inclusion when substantive but flag peer-review status.

### 5.1 LLM + verifier feedback (closest to JML Inferrer in *intent*)

Lemur, Loopy, LaM4Inv, iRank, Quokka, Reasoning+SMT — all covered in §4.6.

### 5.2 LLM-driven whole-spec synthesis

**Ma, Liu, Bu, Chen & Li (2025).** SpecGen: Automated Generation of Formal Program Specifications via Large Language Models. *ICSE 2025*. DOI: 10.1109/ICSE55347.2025.00129. arXiv:2401.08807. — **Most direct head-to-head competitor.** Two-phase: (1) LLM-driven generation, (2) deterministic mutation when LLM fails. 279/385 (72.5%) verified on Java/JML and C/ACSL. Java subset: 100/120. Outperforms Houdini and Daikon. The contrast for the article: SpecGen needs LLM API calls and verifier-driven mutation; JML Inferrer is offline, deterministic, and zero-cost-per-method.

**Wen, You, Lyu, Lin, Lu & Liu (2024).** Enchanting Program Specification Synthesis by Large Language Models using Static Analysis and Program Verification. *CAV 2024*. arXiv:2404.00762. — *AutoSpec. Hierarchical decomposition; 199/251 (79%) verified within 5 attempts. Outperforms SpecGen on overlapping programs.*

**Anonymous (2026).** AutoReSpec: A Framework for Generating Specification using Large Language Models. arXiv:2604.03758. — *Open + closed LLM ensemble; 67/72 (93%) pass.*

**Greif et al. (2024).** Automated Generation of Code Contracts: Generative AI to the Rescue? *GPCE 2024*. — *Fine-tunes CodeT5/CodeT5+ on 14k annotated Java methods. ~66% exact-match; >80% LCS overlap; >95% well-formed. The closest published Java-specific LLM-spec baseline.*

**Anonymous (2025).** Beyond Postconditions: Can Large Language Models Infer Formal Contracts for Java Methods? arXiv:2510.12702. — *Recent direct benchmark of LLM contract inference on Java.*

**Teuber & Beckert (2025).** Next Steps in LLM-Supported Java Verification. arXiv:2502.01573. — *KIT. Mixed-strategy meta-algorithm with KeY proof-tree feedback. ~90% loop-invariant synthesis success. Direct head-to-head positioning material: LLM-driven JML synthesis using a different verifier (KeY) than OpenJML.*

**Endres, Fakhoury, Chakraborty & Lahiri (2024).** Can Large Language Models Transform Natural Language Intent into Formal Method Postconditions? *PACMSE 2024 (FSE)*. arXiv:2310.01831. — *nl2postcond. 77–96% correct postconditions; LLM postconditions catch 64 real bugs in Defects4J v2.0.0. Important contrast: requires NL Javadoc input; JML Inferrer requires only source.*

**Zhang et al. (2025).** Breaking the Myth: Can Small Models Infer Postconditions Too? arXiv:2507.10182.

### 5.3 Class-invariant synthesis

**Anonymous (2025).** ClassInvGen: Class Invariant Synthesis using Large Language Models. arXiv:2502.18917 / OpenReview. — **Direct competitor for the class-invariant sub-task.** Co-generates class invariants and filtering test suites; 77% pass rate against unit tests, 100% with co-generation.

### 5.4 Verified code synthesis (LLM emits both code + spec)

**Sun, Sheng, Padon & Barrett (2024).** Clover: Closed-Loop Verifiable Code Generation. *SAIV 2024*. arXiv:2310.17807. — *Reduces correctness checking to consistency among code, docstrings, formal annotations. Dafny. 87% acceptance, zero false positives on adversarial.*

**Yang et al. (2025).** AutoVerus: Automated Proof Generation for Rust Code. *PACMPL 2025*. arXiv:2409.13082. — *Multi-agent system; >90% of 150 Verus tasks proven.*

**Chen et al. (2025).** SAFE / Self-Evolving AutoVerus. *ICLR 2025*.

**Aggarwal, Parno et al. (2024/25).** AlphaVerus: Bootstrapping Formally Verified Code Generation through Self-Improving Translation and Treefinement. *ICML 2025*. arXiv:2412.06176.

**Bakšys et al. (2025/26).** ATLAS: Automated Toolkit for Large-Scale Verified Code Synthesis. arXiv:2512.10173.

**Loughridge, Sun et al. (2024).** DafnyBench: A Benchmark for Formal Software Verification. arXiv:2406.08467; NeurIPS 2024 D&B. — *782-program Dafny benchmark. Best model (Claude 3 Opus) ~68%.*

**Anonymous (2025).** VeriBench: End-to-End Formal Verification Benchmark for AI Code Generation in Lean 4. *ICML 2025*. — *113 tasks; agentic Trace ~60%.*

**Misu et al. (2024).** Towards AI-Assisted Synthesis of Verified Dafny Methods. *PACMSE 2024*.

### 5.5 LLM theorem proving (orthogonal)

**First, Rabe, Ringer & Brun (2023).** Baldur: Whole-Proof Generation and Repair with Large Language Models. *ESEC/FSE 2023*. arXiv:2303.04910.

**Polu & Sutskever (2020).** Generative Language Modeling for Automated Theorem Proving. arXiv:2009.03393. — *GPT-f; first transformer-based prover for Metamath.*

**Yang, Swope, Gu et al. (2023).** LeanDojo: Theorem Proving with Retrieval-Augmented Language Models. *NeurIPS 2023*. arXiv:2306.15626.

**Song et al. (2024).** Lean Copilot. arXiv:2404.12534.

**DeepSeek-AI (2025).** DeepSeek-Prover-V2. arXiv:2504.21801. — *88.9% on MiniF2F-test.*

**Kozyrev et al. (2024).** CoqPilot. *ASE 2024 Tool Demo*. arXiv:2410.19605.

**Mugnier et al. (2024).** Laurel: Unblocking Automated Verification with Large Language Models. arXiv:2405.16792. — *LLM generates helper assertions in Dafny.*

### 5.6 ACSL/Frama-C specific

**Granberry et al. (2024).** Specify What? Enhancing Neural Specification Synthesis by Symbolic Methods. *SEFM 2024*. arXiv:2406.15540. — **Closest philosophical sibling.** LLM prompts augmented with Pathcrawler (concolic) and EVA (abstract interpretation).

**Granberry et al. (2025).** Seeking Specifications: The Case for Neuro-Symbolic Specification Synthesis. *Formal Aspects of Computing 2025*. arXiv:2504.21061. — *Position paper; useful to cite when arguing for hybrid design space.*

**Anonymous (2026).** Evaluating LLM-Generated ACSL Annotations for Formal Verification. arXiv:2602.13851.

**Anonymous (2025).** Integrating Symbolic Execution with LLMs for Automated Generation of Program Specifications. arXiv:2506.09550. — *SymPro.*

### 5.7 Smart contract spec synthesis (analogue)

**Liu et al. (2024).** PropertyGPT: LLM-driven Formal Verification of Smart Contracts through Retrieval-Augmented Property Generation. *NDSS 2025*. arXiv:2405.02580. — *80% recall; detected 26/37 CVEs and 12 zero-days.*

**Anonymous (2025).** FLAMES: Fine-tuning LLMs to Synthesize Invariants for Smart Contract Security. arXiv:2510.21401. — *Largest-scale fine-tuned spec model to date (514,506 verified contracts).*

### 5.8 Surveys and position papers

**Hou, Zhao, Liu, Yang, Wang, Li, Luo, Lo, Grundy & Wang (2024).** Large Language Models for Software Engineering: A Systematic Literature Review. *ACM TOSEM 2024*. — **Mandatory survey citation.** 947 studies, 112 SE tasks.

**iSEngLab (2025).** A Survey on Large Language Models for Software Engineering. *SCIS 2025*.

**Fan, Gokkaya, Harman, Lyubarskij, Sengupta, Yoo & Zhang (2023).** Large Language Models for Software Engineering: Survey and Open Problems. *ICSE-FoSE 2023*.

**Anonymous (2025).** Leveraging LLMs for Formal Software Requirements: Challenges and Prospects. *VERIFYAI / CEUR-WS Vol-4142 paper 11.* arXiv:2506.11874. — *Mentions JML and OpenJML; cite for concurrent vision.*

**Anonymous (2024).** Fusion of LLMs and Formal Methods for Trustworthy AI Agents. arXiv:2412.06512.

**Anonymous (2024).** LLM-guided Predicate Discovery and Data Augmentation. *ICSE 2025*. DOI: 10.1145/3672608.3707984. — *Closest analogue to the dev-time probe workflow.*

---

## 6. NL-driven specification inference

**Tan, Marinov, Tan & Leavens (2012).** @tComment: Testing Javadoc Comments to Detect Comment-Code Inconsistencies. *ICST 2012*, 260–269. DOI: 10.1109/ICST.2012.106.

**Goffi, Gorla, Ernst & Pezzè (2016).** Automatic Generation of Oracles for Exceptional Behaviors. *ISSTA 2016*, 213–224. DOI: 10.1145/2931037.2931061. — *Toradocu.*

**Blasi, Goffi, Kuznetsov, Gorla, Ernst, Pezzè & Castellanos (2018).** Translating Code Comments to Procedure Specifications. *ISSTA 2018*, 242–253. DOI: 10.1145/3213846.3213872. — *JDoctor; 92% precision / 83% recall on translating comments to specs.*

**Zhong, Zhang, Xie & Mei (2009, 2011).** Inferring Resource Specifications from Natural Language API Documentation. *ASE 2009*, 307–318; *ASE Journal* 18(2), 227–261. — *Doc2Spec.*

**Zhai, Shi, Pan, Zhou, Liu, Fang, Ma, Tan & Zhang (2020).** C2S: Translating Natural Language Comments to Formal Program Specifications. *ESEC/FSE 2020*, 25–37. DOI: 10.1145/3368089.3409716.

---

## 7. Specification-based test generation

### 7.1 Bounded-exhaustive and constraint-driven

**Boyapati, Khurshid & Marinov (2002).** Korat: Automated testing based on Java predicates. *ISSTA 2002*, 123–133. DOI: 10.1145/566171.566191. — *SIGSOFT Distinguished Paper / Impact Paper.*

**Cheon & Leavens (2002).** A simple and practical approach to unit testing. *ECOOP 2002*. — *JMLUnit.*

**Zimmerman & Nagmoti (2010).** JMLUnit: The Next Generation. *FoVeOOS 2010*. — *JMLUnitNG.*

### 7.2 Symbolic execution and bytecode analysis

**Cadar, Dunbar & Engler (2008).** KLEE: Unassisted and Automatic Generation of High-Coverage Tests for Complex Systems Programs. *OSDI 2008*, 209–224. — *>90% line coverage on 89 GNU coreutils; 56 bugs in 452 applications.*

**Visser, Pasareanu & Khurshid (2004).** Test Input Generation with Java PathFinder. *ISSTA 2004*, 97–107. DOI: 10.1145/1007512.1007526.

**Anand, Pasareanu & Visser (2007).** JPF-SE: A Symbolic Execution Extension to Java PathFinder. *TACAS 2007*, LNCS 4424, 134–138. DOI: 10.1007/978-3-540-71209-1_12.

**Tillmann & de Halleux (2008).** Pex – White Box Test Generation for .NET. *TAP 2008*, LNCS 4966, 134–153. DOI: 10.1007/978-3-540-79124-9_10. — *Shipped as IntelliTest in Visual Studio 2015.*

**Tillmann, de Halleux & Xie (2010).** Parameterized Unit Testing. *ICSE 2010*, 483–484. DOI: 10.1145/1810295.1810441.

**Braione, Denaro, Mattavelli & Pezzè (2017).** Combining Symbolic Execution and Search-Based Testing for Programs with Complex Heap Inputs. *ISSTA 2017*, 90–101. — *SUSHI.*

**Braione, Denaro, Mattavelli & Pezzè (2018).** SUSHI: A Test Generator for Programs with Complex Structured Inputs. *ICSE 2018 Companion*, 21–24. DOI: 10.1145/3183440.3183472.

### 7.3 Random testing with contracts

**Pacheco, Lahiri, Ernst & Ball (2007).** Feedback-Directed Random Test Generation. *ICSE 2007*, 75–84. DOI: 10.1109/ICSE.2007.37. — *Randoop.*

**Pacheco & Ernst (2005).** Eclat: Automatic Generation and Classification of Test Inputs. *ECOOP 2005*, LNCS 3586, 504–527. DOI: 10.1007/11531142_22. — **Most directly aligned with the bug-detection thesis: Daikon-mined invariants as oracles for randomly generated tests.**

**Csallner & Smaragdakis (2004).** JCrasher: An Automatic Robustness Tester for Java. *Software: Practice and Experience*, 34(11), 1025–1050. DOI: 10.1002/spe.602.

### 7.4 Search-based test generation

**Fraser & Arcuri (2011).** EvoSuite: Automatic Test Suite Generation for Object-Oriented Software. *ESEC/FSE 2011*, 416–419. DOI: 10.1145/2025113.2025179.

**Fraser & Arcuri (2013).** Whole Test Suite Generation. *IEEE TSE*, 39(2), 276–291. DOI: 10.1109/TSE.2012.14.

**Fraser & Arcuri (2015).** 1600 Faults in 100 Projects. *Empirical Software Engineering*, 20(3), 611–639. DOI: 10.1007/s10664-013-9288-2.

**Almasi, Hemmati, Fraser, Arcuri & Benefelds (2017).** An Industrial Evaluation of Unit Test Generation: Finding Real Faults in a Financial Application. *ICSE-SEIP 2017*, 263–272. DOI: 10.1109/ICSE-SEIP.2017.27.

### 7.5 Property-based testing and fuzzing

**Claessen & Hughes (2000).** QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs. *ICFP 2000*, 268–279. DOI: 10.1145/351240.351266.

**Padhye, Lemieux & Sen (2019).** JQF: Coverage-Guided Property-Based Testing in Java. *ISSTA 2019*, 398–401. DOI: 10.1145/3293882.3339002.

**Padhye, Lemieux, Sen, Papadakis & Le Traon (2019).** Semantic Fuzzing with Zest. *ISSTA 2019*, 329–340. DOI: 10.1145/3293882.3330576.

**Nilizadeh, Leavens & Cok (2024).** JMLKelinci+: Detecting Semantic Bugs and Covering Branches with Valid Inputs Using Coverage-Guided Fuzzing and Runtime Assertion Checking. *Formal Aspects of Computing*, 36(2), Article 8. DOI: 10.1145/3607538. — **Conceptually exactly the back-end that should consume inferred JML.** Preconditions filter inputs; postconditions detect bugs.

**Kersten, Luckow & Pasareanu (2017).** POSTER: AFL-based Fuzzing for Java with Kelinci. *CCS 2017*, 2511–2513. DOI: 10.1145/3133956.3138820.

### 7.6 Industrial / model-based testing

**Veanes, Campbell, Grieskamp, Schulte, Tillmann & Nachmanson (2008).** Model-Based Testing of Object-Oriented Reactive Systems with Spec Explorer. *Formal Methods and Testing*, LNCS 4949, 39–76. — *Microsoft.*

**Parasoft Corporation (2024).** Parasoft Jtest — Java Unit Testing Tool. — *Industrial precedent.*

### 7.7 Oracle synthesis from inferred specs

**Dinella, Ryan, Mytkowicz & Lahiri (2022).** TOGA: A Neural Method for Test Oracle Generation. *ICSE 2022*, 2130–2141. DOI: 10.1145/3510003.3510141. — *Combined with EvoSuite, found 57 real bugs in large-scale Java, 30 not found by any other automated method.*

---

## 8. Spec-driven bug detection (the thesis line)

The papers that most directly support "FAILED outcome on inferred specs implies a real bug" reading.

**Engler, Chen, Hallem, Chou & Chelf (2001).** Bugs as Deviant Behavior. *SOSP 2001*. — **Foundational.**

**Xie & Notkin (2003, 2006).** Mutually Enhancing Test Generation and Specification Inference. *FATES 2003*, LNCS 2931, 60–69. DOI: 10.1007/978-3-540-24617-6_5. *ASE Journal* 13(3), 345–371. DOI: 10.1007/s10515-006-8530-6. — **Coins the mutual-enhancement framing.**

**Csallner & Smaragdakis (2008).** DSD-Crasher: A Hybrid Analysis Tool for Bug Finding. *ACM TOSEM*, 17(2), Article 8. — **Architectural model: Daikon → ESC/Java → JCrasher.**

**Csallner & Smaragdakis (2005).** Check 'n' Crash: Combining Static Checking and Testing. *ICSE 2005*, 422–431. DOI: 10.1145/1062455.1062533.

**Pacheco, Lahiri & Ball (2008).** Finding Errors in .NET with Feedback-Directed Random Testing. *ISSTA 2008*, 87–96. DOI: 10.1145/1390630.1390643.

**Pradel & Gross (2009, 2012).** Automatic Generation of Object Usage Specifications from Large Method Traces. *ASE 2009*, 371–382. DOI: 10.1109/ASE.2009.60. *Statically Checking API Protocol Conformance with Mined Multi-Object Specifications*. *ICSE 2012*, 925–935. DOI: 10.1109/ICSE.2012.6227127.

**Pradel & Gross (2012).** Leveraging Test Generation and Specification Mining for Automated Bug Detection without False Positives. *ICSE 2012*, 288–298. DOI: 10.1109/ICSE.2012.6227185. — **Direct precedent: violations of inferred specs as bugs by construction.**

**Le, Raad, Villard, Berdine, Dreyer & O'Hearn (2022).** Finding Real Bugs in Big Programs with Incorrectness Logic. *PACMPL (OOPSLA 2022)*, 6(OOPSLA1), 81:1–81:27. DOI: 10.1145/3527325.

**O'Hearn (2020).** Incorrectness Logic. *POPL 2020*. *PACMPL* 4(POPL), 10:1–10:32. DOI: 10.1145/3371078. — *Frames bug-detection as: infer an under-approximate post-condition for an error.*

**Raad, Berdine, Dang, Dreyer, O'Hearn & Villard (2020).** Local Reasoning About the Presence of Bugs: Incorrectness Separation Logic. *CAV 2020*, LNCS 12225, 225–252. DOI: 10.1007/978-3-030-53291-8_14.

**Dallmeier, Knopp, Mallon, Fraser, Hack & Zeller (2012).** Automatically Generating Test Cases for Specification Mining. *IEEE TSE*, 38(2), 243–257. DOI: 10.1109/TSE.2011.105. — *TAUTOKO; iterative inference + tests + richer inference.*

---

## 9. Surveys, retrospectives, and benchmarks

### 9.1 JML retrospectives

**Burdy, Cheon, Cok, Ernst, Kiniry, Leavens, Leino & Poll (2005).** An overview of JML tools and applications. *STTT* 7(3), 212–232. — **Mandatory.**

**Chalin, Kiniry, Leavens & Poll (2006).** Beyond Assertions: Advanced Specification and Verification with JML and ESC/Java2. *FMCO 2005*, LNCS 4111, 342–363. DOI: 10.1007/11804192_16.

**Leavens & Clifton (2008).** Lessons from the JML Project. *VSTTE 2005*, LNCS 4171, 134–143. DOI: 10.1007/978-3-540-69149-5_15.

**Leavens, Cok & Nilizadeh (2022).** Further Lessons from the JML Project. *The Logic of Software*, LNCS 13360, 309–325. DOI: 10.1007/978-3-031-08166-8_15. — **Most up-to-date citable assessment.**

**Klamroth, Beckert, Kirsten & Ulbrich (2022).** The Karlsruhe Java Verification Suite. *The Logic of Software*, LNCS 13360, 290–308. DOI: 10.1007/978-3-031-08166-8_14.

**Robby & Chalin (2009).** Preliminary design of a unified JML representation and software infrastructure. *FTfJP 2009*, Article 4. DOI: 10.1145/1557898.1557903. — *JIR.*

**Cok & Johnson (2014).** SPEEDY: An Eclipse-based IDE for invariant inference. *F-IDE 2014*. EPTCS 149, 44–58. arXiv:1404.6605. — *Documents Cok's planned roadmap for OpenJML invariant discovery.*

### 9.2 Verification competitions

**Huisman, Klebanov & Monahan (2015).** VerifyThis 2012. *STTT* 17(6), 647–657. DOI: 10.1007/s10009-015-0396-8.

**Ernst, Huisman, Mostowski & Ulbrich (2022).** VerifyThis 2019. *STTT* 24, 783–806. DOI: 10.1007/s10009-021-00619-x.

**Beyer (2023, 2024).** Competition on Software Verification and Witness Validation: SV-COMP 2023, 2024. *TACAS 2023*, LNCS 13994, 495–522; *TACAS 2024*, LNCS 14572, 299–329. — **Standard Java verification benchmark.**

**Beyer & Kanav (2018).** Benchmarking of Java Verification Tools at SV-COMP. arXiv:1809.03739.

### 9.3 Cross-cutting surveys

**Robillard, Bodden, Kawrykow, Mezini & Ratchford (2013).** Automated API Property Inference Techniques. *IEEE TSE* 39(5), 613–637. — **Mandatory for spec-mining context.**

**Lo, Khoo, Han & Liu (eds.) (2011).** Mining Software Specifications. CRC Press.

**Barr, Harman, McMinn, Shahbaz & Yoo (2015).** The Oracle Problem in Software Testing: A Survey. *IEEE TSE*, 41(5), 507–525. DOI: 10.1109/TSE.2014.2372785. — *Canonical oracle survey.*

**Estler, Furia, Nordio, Piccioni & Meyer (2014).** Contracts in Practice. *FM 2014*, LNCS 8442, 230–246. DOI: 10.1007/978-3-319-06410-9_17. — *21 Eiffel/Java/C# projects; contracts evolve with code, only a small fraction of methods carry them.*

**Schiller, Donohue, Coward & Ernst (2014).** Case Studies and Tools for Contract Specifications. *ICSE 2014*, 596–607. DOI: 10.1145/2568225.2568285.

**Dietrich & Müller (2017).** Contracts in the Wild: A Study of Java Programs. *ECOOP 2017*, LIPIcs 74, 9:1–9:29. DOI: 10.4230/LIPIcs.ECOOP.2017.9.

**Just, Jalali, Inozemtseva, Ernst, Holmes & Fraser (2014).** Are Mutants a Valid Substitute for Real Faults in Software Testing? *FSE 2014*, 654–665. DOI: 10.1145/2635868.2635929.

**Nimmer & Ernst (2002).** Invariant Inference for Static Checking: An Empirical Evaluation. *FSE 2002*, 11–20. DOI: 10.1145/587051.587054. — **Methodologically essential for evaluation protocol design.**

**Hou et al. (2024).** LLMs for Software Engineering: SLR. *ACM TOSEM 2024*. — *947 studies.*

---

## 10. Where the JML Inferrer fits

### 10.1 Closest comparators (must-cite head-to-head)

| Comparator | What it does differently | Position in article |
|---|---|---|
| **Houdini** (2001) | Template-pool + verifier filtering; ESC/Java only; abandoned | Closest classical ancestor; cite as "the canonical guess-and-check approach we extend with AST-driven candidate generation." |
| **Daikon** (2001/2007) | Dynamic, templates, statistical filtering | The dominant baseline; cite as "the dominant alternative spec-inference paradigm; differs in source of evidence (traces vs. AST)." |
| **DynaMate** (2014/15) | Postcondition mutation + dynamic + ESC/Java2; assumes user postcondition | Cite as "the closest precedent in the JML ecosystem; differs in input requirement (we infer the postcondition rather than mutate it)." |
| **EvoSpex** (2021) | Evolutionary postcondition learning over JML-like grammar | Direct competitor for postconditions; differs in search-based vs. heuristic-AST mechanism. |
| **SpecGen** (2024/25) | LLM + verifier-driven mutation; OpenJML | Most direct contemporary competitor; differs in cost (LLM API per method vs. zero-cost AST pass). The user has explicitly deferred LLM augmentation in the inferrer; SpecGen serves as the LLM baseline. |

### 10.2 Tier-2 comparators (cite for completeness)

- **Furia & Meyer (2010)** — postcondition-mutation rules; the conceptual ancestor of the inferrer's loop-invariant heuristics.
- **Clousot / CodeContracts** (Fähndrich & Logozzo 2010) — abstract-interpretation contract checking on .NET; the principled alternative.
- **PIE / LoopInvGen** (Padhi et al. 2016) — data-driven precondition inference with feature synthesis; SyGuS-Comp-winner baseline.
- **AutoSpec** (Wen et al. 2024) — LLM + static analysis + verifier feedback for ACSL; the C/ACSL counterpart of SpecGen.
- **Code2Inv / CLN2INV / G-CLN** — neural baselines for loop-invariant inference; cite to show awareness without claiming to compete on Code2Inv-style numerical benchmarks.
- **Lemur / Loopy / LaM4Inv / iRank** — LLM-loop-invariant family; cite as the active research frontier the user has deliberately deferred.

### 10.3 Tier-3 (cite once, in passing)

- The IC3/PDR / SeaHorn / Spacer family — different verification idiom (Horn clauses).
- The full FSM-mining literature (Ammons, Perracotta, GK-tail, Synoptic, Texada) — different output (FSAs vs. value-space contracts).
- Bi-abduction / Pulse / Infer — separation logic at scale.
- The full LLM theorem-proving literature (Baldur, Lean Copilot, DeepSeek-Prover) — orthogonal problem.

### 10.4 Distinguishing claims for the article

1. **Architectural novelty.** Pure heuristic AST pattern matching as the primary engine, without templates, fixpoints, traces, or LLM, is unusual. Closest precedents are DynaMate (which mutates the user's postcondition) and Furia & Meyer 2010 (postcondition-mutation rules). No continuously maintained tool occupies exactly this point.
2. **Cost profile.** O(LOC) inference cost with no per-method verifier loop (until OpenJML downstream), no LLM API calls, no test execution, no SMT search during inference. Reproducibility and determinism follow.
3. **Spec breadth.** Most comparators infer one spec class (Daikon emphasises invariants; DynaMate emphasises loop invariants given postconditions; SpecGen emphasises whole-method contracts). The JML Inferrer covers preconditions, postconditions, loop invariants, class invariants, and frame conditions in tandem.
4. **JML-specific emission.** Most inference work targets a different output language. The JML Inferrer emits valid JML syntax with correct quantifier scoping, no natural-language fallback, with decisions that respect OpenJML's ESC pipeline (`code-math=safe`, `spec-math=bigint`, the OpenJML fork's `define-fun-rec` for `\sum`/`\product`/`\num_of`).
5. **Bug-detection framing.** Aligns with Engler 2001, Xie & Notkin 2003/2006, DSD-Crasher 2008, Pradel & Gross 2012: a FAILED OpenJML outcome on inferred specs is candidate evidence of a method bug. The empirical question is the rate at which this holds — measurable via the existing verification suite plus targeted real-bug benchmarks.

---

## 11. Open problems and gaps the JML Inferrer addresses

### 11.1 Gaps in the prior JML inference literature

- **Loop invariants without user postconditions.** DynaMate and Furia & Meyer require a postcondition to mutate. The JML Inferrer infers both.
- **JML emission with frame conditions.** Most inference tools omit `assignable` clauses; Kogtenkov-Meyer-Velder addressed this for Eiffel only. The JML Inferrer emits frame conditions in tandem.
- **OpenJML 2021+ compatibility.** Houdini/ESC/Java2 are abandoned; the JML Inferrer is a current OpenJML client.
- **Class-invariant inference for Java.** Pasareanu's symbolic-execution-based work and recent LLM-based ClassInvGen are the only serious entries; the JML Inferrer's `ClassInvariantInferrer` adds heuristic AST-based class-invariant inference.

### 11.2 Acknowledged limits (likely Reviewer-2 ammunition)

- **No fixpoint.** Cannot infer invariants whose form was not anticipated by a pattern. Polyhedra/octagons can; the JML Inferrer cannot.
- **No CEGAR loop.** When a candidate fails to verify, no automatic refinement. Houdini's elimination loop is a missing feature; future work.
- **No polynomial invariants.** DIG, G-CLN, Aligator can; the JML Inferrer cannot.
- **No quantified array invariants beyond fixed templates.** FreqHorn-quantified-SyGuS can discover novel forms; the JML Inferrer's `(\forall int k; ...; arr[k] PRED)` emission is restricted to recognized predicates.
- **Test-coverage independence is a strength but also a limit.** Daikon catches data-dependent invariants the JML Inferrer cannot anticipate.

### 11.3 Future hybrid directions (consistent with the deferred LLM stance)

- **Houdini-style elimination loop.** When OpenJML rejects a candidate, drop only the failing clause rather than the whole spec.
- **Abstract-interpretation fallback for numeric facts.** Apron-style intervals/octagons could supply invariants the heuristic missed.
- **LLM as dev-time probe (already piloted 2026-04-30).** Recorded in `feedback_ai_probe_workflow.md`; preserves heuristic-AST inference at runtime.
- **Symbolic-execution post-processing.** SymInfer/DySy-style path-condition synthesis could augment the heuristic for hard cases.

---

## Appendix A: Citation completeness audit

Total distinct entries cited: ≈180 across nine categories.

Verified by automated search (DOI/arXiv/URL anchored); preserved verbatim from the agents' responses where available. Approximately 12 entries are unrefereed arXiv preprints, flagged in-text. Several entries marked "Anonymous" reflect double-blind preprints whose author lists were not yet public at the time of the agent's search; these should be re-checked before submission.

## Appendix B: Suggested citation density for the journal article

For a JSEP/Wiley-class paper, recommended density:

- **Heavy (cited multiple times):** Houdini, Daikon, DynaMate, Furia & Meyer 2010, FreqHorn, OpenJML, KeY, Burdy 2005, Leavens-Cok-Nilizadeh 2022, Engler 2001, Xie & Notkin 2003.
- **Medium:** Cousot–Cousot 1977, Karr 1976, Cousot–Halbwachs 1978, ICE-DT, PIE/LoopInvGen, EvoSpex, SpecGen, AutoSpec, Lemur, Loopy, Eclat, JMLUnitNG, JMLKelinci+, Pradel-Gross 2012.
- **Light (cited for completeness):** the Horn-clause family (Bradley, Spacer, SeaHorn), the FSM-mining family (Ammons, Perracotta, Synoptic, Texada), bi-abduction/Infer, DafnyBench/VeriBench, Lean Copilot/Baldur/DeepSeek-Prover.

## Appendix C: Open candidates for benchmark comparison

Useful Java/JML benchmark suites to compare against:

- SpecGenBench (120 Java programs; SpecGen 2025)
- Defects4J v2.0.0 (real Java bugs; nl2postcond used this)
- SV-COMP Java track (586+ tasks, 2023–2024)
- VerifyThis problems (annual; KeY/Dafny/Coq solutions available)
- DafnyBench (782 Dafny programs; comparable for "spec inference + verification" framing)
- 26 java.util methods (the DynaMate benchmark)
