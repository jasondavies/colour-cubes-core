all: check

check:
	lake build
	python3 scripts/check.py

.PHONY: all check
