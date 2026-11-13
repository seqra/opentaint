# OpenTaint CLI style guide

The CLI follows the [Command Line Interface Guidelines](https://clig.dev). This guide holds only
the choices that they leave open. Help is a short reference, background goes in the docs, next
steps go in the output.

## Commands and flags

- A flag has the same name in every command that has it, and the same description when it does
  the same
- A flag that takes several values is repeatable. No comma-separated lists
- Shared names: `-o`, `--output` for the path of the result, `--dry-run`, `--yes` for the prompt

## Help

- Usage: `<arg>` required, `[<arg>]` optional, `<arg>...` repeatable
- A placeholder is in lowercase kebab-case and names the thing, not its type: `<source-path>`, not
  `<path>`. Write it the same way, brackets included
- Short: a verb phrase in the imperative, capitalized, at most ~60 characters
- Long: one sentence, usually the Short as a sentence. A second sentence only when it is not
  clear when the command is needed. No flags, steps, definitions, internals, exit codes, or
  filler. A group has no Long
- Arguments: one line for each positional argument, with the default when it is optional
- The commands, the flags, and the global flags start their descriptions in one column
- Write a paragraph as one line: the help wraps it at the terminal width, at most 80 columns.
  Break a long example by hand with `\`
- Examples: a command for a main task shows the plain run and one or two common variants. Other
  commands have examples only when the use is not obvious. An example is a `#` comment with the
  goal, then one command
- Examples run from the project root and use the paths of the skills: `.opentaint/project`,
  `.opentaint/rules`, `.opentaint/dataflow`, `.opentaint/pass-through`,
  `.opentaint/results/report.sarif`, `.opentaint/test-projects/<name>`,
  `.opentaint/test-compiled/<name>`
- A made-up value looks made up: `com.example`. A value that names a real library or rule is real

## Flag descriptions

- One short phrase, capitalized. The help does not wrap the rows of the flags, so keep it short
- A flag that names an input or an output is a noun phrase: `Path to the SARIF report`. A flag
  that changes what the command does is a verb phrase: `Skip the confirmation prompt`
- A flag with a closed set of values lists them: `Color mode: auto, always, or never`
- Notes go at the end, in this order: `(e.g. 30m, 1h)`, `(0 = unlimited)`, `(repeatable)`,
  `(required)`, `(default: ...)`. Write the default only when cobra does not print it
- No backticks: pflag prints the first backticked word as the name of the value of the flag
- The same rules hold for the flags that cobra adds, such as `--help`

## Output

- A run prints what it is going to do, the progress, the result, and the next steps, with one
  blank line between the parts
- Progress is a spinner for each long step, named in the -ing form with no article or ellipsis:
  `Compiling project model`. It ends with `✓` or `✗`. Without a terminal there is no spinner and
  no progress line
- A result of one value is one line in the past tense: ``Created the project model at `x` ``. A
  result of two values or more is a block
- When there is nothing to show, say so in one line
- The notice of a new version is an exception to the next steps: one line after the output,
  ``A new version is available: v1.2.3. To update, run `opentaint update` ``
- Check the inputs before the long step starts, so that a wrong input does not look like a
  failed step
- A path in a block is absolute. In a message and in a next step, a path and a value are as the
  user wrote them: `--timeout 2m`, not `2m0s`

### Highlighting

- The theme colors the `Error:` or `Warning:` line, the result line of a success, the title and
  the keys of a block, the goal of a next step, and a count by severity. The command of a next
  step is bold. Values, paths, and causes are plain. A command does not style text itself
- `✓` and `✗` mark a finished step. No emoji, and no capitals or bold for emphasis
- In a sentence, backticks mark a command line, a file, a path, and a literal value:
  `opentaint compile`, `rule-test.yaml`, `builtin`. A flag and a placeholder stand as they are:
  --output, <source-path>
- No backticks or quotes around a value that stands alone: after a key or in a next step

### Blocks

- A block has a short title in Title Case. A total goes last
- Each item is `Key: value`. A key is a short noun phrase: `Project model`, not
  `Project model written to`. Within a block, put every value either after its key or on its own
  line under it
- A group is a key with items under it. A count or a size of the whole group is the value of the
  key, and the items do not repeat what the key says
- A long list shows its first items and `... and N more`. A flag shows the whole list

### Next steps

- The steps go in a block titled `Suggestions`
- Up to 3 steps, each a goal and a command: `To <goal>, run:`. A step that points to a file or a
  page has its path or URL in place of the command: `To see the full details, open the log:`,
  `To learn more about <topic>, see:`. A step with nothing to paste is one sentence
- Give a step when the result feeds the next command, after a dry run, and after a failure that
  a log or another input can help with. Give none when there is nothing left to do, when the
  user declined the prompt, or when the step repeats what the output shows
- A command in a step works when pasted. Use a placeholder only for a value that the CLI cannot
  know, with the name that the help uses for it. A placeholder can be a part of a path:
  `.opentaint/test-compiled/<name>`

## Errors and warnings

- The message starts with a capital and says what failed, in the words of the user, not of the
  code: `Failed to load the SARIF report`, ``Invalid --color value `sometimes` ``
- The causes go under the message, one on each line:

  ```
  Error: Failed to load the SARIF report
    open report.sarif: no such file or directory
  ```

- An error in the code is lowercase and does not repeat the message of its caller
- What to do goes in the next steps, not in the message. Only the valid values of a flag follow
  a wrong one: ``Invalid --color value `sometimes`, use auto, always, or never``
- A warning says what the command did or found that the user may not expect. It has the form of
  an error, with the causes under it, and tells what the command did in the past tense:

  ```
  Warning: Replaced the build file of `.opentaint/test-projects/my-rule/sinks`
    the new build file has only the libraries from --dependency
  ```

- A usage error, such as an unknown flag or command, ends with ``Run `<command> --help` for
  usage``, the help of the command that the user ran. A mistyped command comes with
  ``Did you mean `<command>`?`` before it
- A renamed command or flag stays as a hidden alias. Using it warns:
  ``Warning: `opentaint compile approximations` is now `opentaint compile models` ``,
  `Warning: --dataflow-approximations is now --dataflow-models`

## Wording

- Short sentences in the active voice. Plain words: "use", not "specify" or "supply". No
  semicolons, "please", "successfully", or exclamation marks
- Sentence case. Title Case only for the titles of blocks and of help sections
- No period after a fragment: Short, a flag description, a key, an example comment. A message of
  one sentence has no period either. A message of several sentences ends each with one
- One term for one concept: project model, model project, dataflow models, built-in ruleset,
  custom ruleset, SARIF report, rule ID. A ruleset is the rules that the analyzer loads together:
  the built-in ruleset or a rules file or directory. A rule is one rule
