.PHONY: docker-build docker-build-debug
artifact.pdf: artifact.tex sigplanconf.cls
	latexmk -pdf -shell-escape artifact.tex

docker-build:
	docker build

docker-build-debug:
	docker build --progress plain .

docker-login:
	docker login

docker-build-and-push:
	docker build -t opencompl-ssa --progress plain .
	docker push siddudruid/opencompl-ssa
