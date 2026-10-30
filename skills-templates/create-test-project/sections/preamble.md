# Skill: Create Test Project

Build a minimal test project whose samples reproduce the flow a rule or model is verified against. A sample routes data between a real library method and the generic taint marker the scaffold provides, with the one verdict it must produce — a positive that must flag, a negative that must not. A test project that builds cleanly is the deliverable: for Java, its compiled model; for Go, the project itself, which the test commands build from source.
