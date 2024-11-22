.PHONY: all clean build cache release

all: release

clean:
	lake clean

build: cache
	lake build

cache:
	lake exe cache get

release:
	@if [ -z "$(VERSION)" ]; then \
    	echo "Error: VERSION is not set. Usage: make release VERSION=<version>"; \
    	exit 1; \
	fi
	gh release create $(VERSION)
	git add .
	git commit -m "$(VERSION)"
	lake publish $(VERSION)
