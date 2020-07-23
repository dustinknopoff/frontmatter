# Frontmatter 

![build-and-check](https://github.com/dustinknopoff/frontmatter/workflows/build-and-check/badge.svg)

A simple, no-dependency library for separating YAML or TOML frontmatter from some text.

For example, Let's say you have a markdown document:

```toml
+++
title = "TOML Frontmatter"
list = [
    "Of",
    "Things",
]
[[assets]]
contentType = "audio/mpeg"
+++

This is some content.
```

```rust
use frontmatter::split_matter;

fn main() {
    let example_text = r#"+++
title = "TOML Frontmatter"
list = [
    "Of",
    "Things",
]
[[assets]]
contentType = "audio/mpeg"
+++"#;
    if let Some((frontmatter, content)) = split_matter(&content) {
        // Do something, probably deserializing the frontmatter in to YAML/TOML
        assert_ne!(f.len(), 0);
        assert_eq!(c, "This is some content.");
    }
}
```

## Installation

Add the following to your `Cargo.toml`

```toml
frontmatter = { git="https://github.com/dustinknopoff/frontmatter", branch="master"}
```