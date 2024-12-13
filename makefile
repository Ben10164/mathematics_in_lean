.PHONY: all release

all: release
change:
	echo "Current version is $(shell grep '^version' lakefile.toml | sed 's/version = "\(.*\)"/\1/')."
	@read -p "Enter the new version: " VERSION; \
	sed -i.bak "s/^version = \".*\"/version = \"$$VERSION\"/" lakefile.toml; \
	echo "Updated version to $$VERSION in lakefile.toml"
release: change
	rm lakefile.toml.bak
	git add .
	git commit -m "$(shell grep '^version' lakefile.toml | sed 's/version = "\(.*\)"/\1/')"
	gh release create $(shell grep '^version' lakefile.toml | sed 's/version = "\(.*\)"/\1/')
	lake upload $(shell grep '^version' lakefile.toml | sed 's/version = "\(.*\)"/\1/')
	git push
