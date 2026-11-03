# Stirling command receiver label loss

The current lowering can remove the generated command-list label at a later, unmarked `List.add` call. The actual Stirling call plan has this sequence. A focused native test reproduces the loss. This is a verified discontinuity between the legacy and bidirectional call paths. The first marked arrival in the full project run was not captured, so this report does not claim that this is its earliest loss.

The measured revision is `e558b496acf82de6ff136325d58f3d90ee5b8559`. No runtime policy changed. The temporary native test was removed after its source, output and XML were saved. The [portable evidence](data/bidirectional-stirling-command-receiver-reset-20261103.json) embeds the selected real call plans, rule metadata, native trace, legacy source excerpts and input hashes.

Stirling-PDF reaches run-8. Run-7 is its latest complete run and accepted forward report. The command ends with a timeout. The native reproducer below is a separate focused run-1 check.

The legacy warning is `java.security.os-command-injection`, at `ProcessExecutor.runCommandWithOutputHandling(List, File)`, Java line 183, `new ProcessBuilder(command)`. Its fingerprint is `wY2lI7b1TEw2RC154xc+UyLWgRr7oi07c8cEICJI+QM=`. The pinned f945 SARIF has one flow with 11 locations. Current Stirling has the same 22 identities as 86ad and 050b; this command identity is one of the three preexisting strict differences from f945.

Use `T` for one accepted full untrusted-data mark. Use `A2` and `A4` for these generated marks:

```text
java/security/command-injection.yaml:os-command-injection;2;$ARGS;2
java/security/command-injection.yaml:os-command-injection;4;$ARGS;2
```

The code and the verified transfer sequence are:

```java
List<String> command = new ArrayList<>();
command.add(runtimePathConfig.getWeasyPrintPath());
command.add(URL);                    // JIR 55
// Source2/source6: CM(arg0,T) -> assign A2/A4 to this.$.
// If the guard holds: P -> command.$/A2 or command.$/A4.
// The SOURCES branch goes directly to REWRITTEN, then binds back.

command.add("--pdf-forms");          // JIR 56
// BIND_IN: command.$/A2 -> this.$/A2.
// The literal supplies no marked input for the source guard.
// UNRESOLVED identity: this.$/A2 reaches RETURNED.
// Return cleanup: remove A2 at this.$; likewise for A4.
// No command.$/A2 or command.$/A4 survives BIND_BACK.

command.add(tempOutputFile.toString());
executor.runCommandWithOutputHandling(command);
// The overload passes command to new ProcessBuilder(command).
```

The real call-56 plan confirms both `UNRESOLVED` stages and no `Callees` stage. Its return-cleanup stage has exact `This` removals for A2 at steps 11 and 27, and A4 at steps 24 and 40. Its generated source condition still has mark checks on argument zero. The mark-aware condition rewriter keeps these checks symbolic, including for the literal call. Thus the reset is present even when that call has no matching marked argument.

The native witness uses the same source and cleanup topology, with one accepted mark leaf. It does not inject demand, cache records or predefined summaries:

```text
source() -> data.$/T
add(data):  CM(arg0,T) -> this.$/A -> command.$/A
[add(literal): this.$/A -> exact return cleanup -> no A]
sink(command): CM(arg0,A)
```

The direct-use control reports. Adding the literal call removes the report. Both runs finish run-1 with `NO_DEMAND_EDGE`; the test result is one pass and one expected retention failure. The trace shows `command.$/A` arriving at the literal statement, then no such fact at the sink statement.

Legacy f945 takes a different path for an unresolved call. It first passes the **caller-local** fact to `unresolvedCallDefaultFactPropagation`. The summary rewriter indexes this source action by `This`. That index does not match the caller-local `command` base, so its default unchanged receiver survives. The pass-rule lane separately maps facts into callee coordinates. Current bidirectional handling binds the receiver to `This` before the unresolved lane and applies the reset there.

The actual lowering audit uses the complete production rules before prescan rule reduction. It confirms the relevant source/reset marks and call resolution, but does not run the whole analysis or reconstruct its source permissions. To prove the exact first loss in the measured project, a further native trace must observe actual T at add-55, its A2/A4 result, and the input and result of add-56. No new handling rule or fix was selected in this investigation.
