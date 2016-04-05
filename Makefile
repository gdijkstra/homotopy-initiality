src=$(shell find . -name \"\*.agda\")

default : all

check-env:
ifndef agda_hott_lib
	$(error Environment variable agda_hott_lib undefined)
endif

all : check-env $(src)
	agda -i. -i$(agda_hott_lib) README.agda
	./todo.sh
