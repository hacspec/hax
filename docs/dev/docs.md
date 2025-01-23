# Docs

## mkdocs material (this page)

Install dependencies

```bash
pip install mkdocs-glightbox mkdocs-nav-weight mkdocs-material
```

[Official docs](https://squidfunk.github.io/mkdocs-material).

### Commands

* `mkdocs new [dir-name]` - Create a new project.
* `mkdocs serve` - Start the live-reloading docs server.
* `mkdocs build` - Build the documentation site.
* `mkdocs -h` - Print help message and exit.

### Project layout

    mkdocs.yml    # The configuration file.
    docs/
        index.md    # The documentation homepage.
        ...         # Other markdown pages, images and other files.
        blog/       # The blog
            posts/  # Blog posts

### Including external files

```
;--8<-- "engine/DEV.md:3:7"
```

--8<-- "engine/DEV.md:3:7"
