all: Main

Main: Main.v Model.v Patterns.v Tools.v
	coqc Tools.v
	coqc Model.v
	coqc Patterns.v
	coqc Main.v

clean:
	rm *.glob *.vo
