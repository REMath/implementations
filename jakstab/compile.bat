@echo off
IF NOT EXIST bin mkdir bin
javac -sourcepath src\ -cp lib\antlr.jar;lib\google-collect-1.0.jar;lib\javabdd-1.0b2.jar -d bin\ src\org\jakstab\*.java %*