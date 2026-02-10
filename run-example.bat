@echo off
echo Building JML Inferrer...
call mvnw.cmd clean package -q

if %ERRORLEVEL% NEQ 0 (
    echo Build failed!
    exit /b 1
)

echo.
echo Running JML Inferrer on example code...
java -jar target\jml-inferrer-1.0.0-jar-with-dependencies.jar experiment\sample_code

echo.
echo Done! Check experiment\sample_code\ to see the generated JML specifications.
pause
