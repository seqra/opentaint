# Skill: Assemble Lib Rules

Source and sink library rules expose open role families through tags. Related custom sources may share a project-specific tag, and a custom join may consume that family with one `tag:` ref. Expand the existing built-in and custom joins first: a created rule that reused a consumed family tag may already be wired without another file. Add only the security joins needed for uncovered source-to-sink combinations, using tags for deliberate family expansion and exact rule refs for isolated components. The joins carry no test project; the main scan verifies them.
