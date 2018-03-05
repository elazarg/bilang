JAR=jars/antlr-4.7-complete.jar
MOD=bilang
BIN=bin
SRCDIR=src/java/$(MOD)
GENDIR=$(SRCDIR)/generated
LANGFILE=BiLang.g4
MANIFEST=$(BIN)/MANIFEST.MF
EXECFILE=bilang.jar

.PHONY: generated clean all manifest

all: generated manifest
	javac -cp $(JAR) -d $(BIN) $(SRCDIR)/*.java $(GENDIR)/*.java
	jar cfm $(EXECFILE) $(MANIFEST) -C $(BIN)/ .

generated: $(LANGFILE)
	java -jar $(JAR) -visitor $(LANGFILE) -package $(MOD).generated -o $(GENDIR)

manifest:
	mkdir -p bin
	echo > $(MANIFEST) "Class-Path: $(JAR) $(BIN)/$(MOD)/*.class $(BIN)/$(MOD)/generated/*.class"
	echo >> $(MANIFEST) "Main-Class: $(MOD).Main"

clean:
	rm -f $(EXECFILE)
	rm -rf $(BIN)/*
	rm -rf $(GENDIR)/*

