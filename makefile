.PHONY: all release update_version

all: release

VERSION := $(shell grep '^version' lakefile.toml | sed 's/version = "\(.*\)"/\1/')

release: update_version
	echo "Current version is $(VERSION)."
	@read -p "Enter the new version: " VERSION; \
	sed -i.bak "s/^version = \".*\"/version = \"$$VERSION\"/" lakefile.toml; \
	echo "Updated version to $$VERSION in lakefile.toml"
	rm lakefile.toml.bak
	git add .
	git commit -m "$(shell grep '^version' lakefile.toml | sed 's/version = "\(.*\)"/\1/')"
	gh release create $(shell grep '^version' lakefile.toml | sed 's/version = "\(.*\)"/\1/')
	lake upload $(shell grep '^version' lakefile.toml | sed 's/version = "\(.*\)"/\1/')
	git push

update_version: