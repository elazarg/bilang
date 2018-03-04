JAR=jars/antlr-4.7-complete.jar
MOD=bilang
BIN=bin
SRCDIR=src/$(MOD)
GENDIR=$(SRCDIR)/generated
LANGFILE=BiLang.g4
MANIFEST=$(BIN)/MANIFEST.MF
EXECFILE=bilang.jar

ANTLR=java -jar $(JAR)
ANTLR_FLAGS=-visitor

.PHONY: generated clean all manifest

all: generated manifest
	javac -cp $(JAR) -d $(BIN) $(SRCDIR)/*.java $(GENDIR)/*.java
	jar cfm $(EXECFILE) $(MANIFEST) -C $(BIN)/ .

generated: $(LANGFILE)
	$(ANTLR) $(ANTLR_FLAGS) $(LANGFILE) -package $(MOD).generated -o $(GENDIR)

manifest:
	echo > $(MANIFEST) "Class-Path: $(JAR) $(BIN)/$(MOD)/*.class $(BIN)/$(MOD)/generated/*.class"
	echo >> $(MANIFEST) "Main-Class: $(MOD).Main"

clean:
	rm -f $(EXECFILE)
	rm -rf $(BIN)/*
	rm -rf $(GENDIR)/*

