# Skill: Assemble Lib Rules

Source and sink library rules are authored per package but never paired across them. Write the security joins that pair them — one per vuln class, each merging the created source/sink rules with the built-ins, mirroring the built-in security rules. The joins carry no test project, the main scan verifies them.
