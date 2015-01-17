### Convenience Makefile for people who don't want to install SBT ###

SRC = Digraph.scala Expr.scala Main.scala Rule.scala VarMap.scala
TARGET = ../lib/ode-gen.jar

.PHONY: clean

all: $(TARGET)

$(TARGET): $(SRC)
	mkdir -p ../lib
	scalac -d $@ $^

clean:
	rm -rf $(TARGET)
