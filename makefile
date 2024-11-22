.PHONY: all clean build cache release

all: release

clean:
	lake clean

build: cache
	lake build

cache:
	lake exe cache get

VERSION := $(shell grep '^version' lakefile.toml | sed 's/version = "\(.*\)"/\1/')

release:
	git add .
	git commit -m "$(VERSION)"
	gh release create $(VERSION)
	lake upload $(VERSION)
	git push
