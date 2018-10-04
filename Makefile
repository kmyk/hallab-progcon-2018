.PHONY: build run json

ExecuteFile := hpc2018/hpc2018.exe

build: $(ExecuteFile)

$(ExecuteFile): Answer.cpp
	[ -L hpc2018/src/Answer.cpp ] || ln -s ../../Answer.cpp hpc2018/src/Answer.cpp
	make -C hpc2018 all

run: $(ExecuteFile)
	make -C hpc2018 run

json: $(ExecuteFile)
	[ -d json ] || mkdir json
	make -C hpc2018 json | awk 'NR==2' > json/$(shell date +%Y-%m-%d-%H-%M-%S-%N).json

viewer:
	browse hpc2018/viewer/index.html
