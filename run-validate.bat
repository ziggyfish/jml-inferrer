@echo off
REM Build the project and run inference + OpenJML validation on sample code

echo Building JML Inferrer...
call mvn clean package -q

if %ERRORLEVEL% neq 0 (
    echo Build failed!
    exit /b 1
)

echo Running inference and validation on sample code...
java -jar target\jml-inferrer-1.0.0-jar-with-dependencies.jar experiment\sample_code --validate
