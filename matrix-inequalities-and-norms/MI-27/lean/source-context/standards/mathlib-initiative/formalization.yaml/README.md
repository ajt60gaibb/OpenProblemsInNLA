# formalization.yaml

A self-reporting standard for formalization projects.

Drop a filled-in `formalization.yaml` at the root of your formalization repo. Fill in the `[required]` fields; the rest are optional. The point is to set an expectation that projects report on what was formalized, how, and how faithfully; without requiring everyone to invent their own format.

## How to use it

1. Copy `formalization.yaml` to the root of your formalization repo.
2. Fill in every field marked `[required]`. Fill in as much of the rest as is useful.

The file is meant to live **alongside the formalization it describes**. That co-location is deliberate: anything the repo already encodes (the Lean toolchain (`lean-toolchain`), dependencies and pins (`lakefile`), build status (CI), commit history) is intentionally *not* duplicated here. This file captures the things that aren't mechanically obvious from the source tree: provenance, intent, process, and how faithfully the formalization tracks its source.

`sources` is required. A project may formalize an article, book, web post,
folklore result, conversation, or other source. When the formalization is the
first presentation of a new theorem, record an `original-proof` source entry
instead. Source entries accept a general identifier or citation rather than
requiring an arXiv record. Use `related_formalizations` separately for formal
proof developments that this project builds on or should be compared with.

Within a source entry, use `authors` only for bibliographic authorship. Use
`contributors` for other credited roles, with one `name` and free-form
`role` per entry; examples include `editor` and `problem-proposer`. Repeat
a person when they have several roles. Distinct works, such as an open-problem
collection and a later solution paper, should still be separate source entries
so that each keeps its own identifier and relationship to the formalization.

When a repository is only a packaging or comparison layer around another
formalization, identify the pinned `repository.substantive_formalization`.
Otherwise omit `repository`: the repository carrying the file is the
substantive development by default. The optional relationship distinguishes
authorship of the wrapper from authorship and maintenance of the formal proof
itself without making ordinary projects restate the obvious.

Use `project.description` for a concise account of the mathematical content
and principal results. Registries and other readers can use it as a public
summary; fuller exposition can remain in the README, source documentation, or
other project material.

For a fully manual project, use `method: manual` under `automation.methods`,
and omit automation-specific fields that do not apply.

## Categories and explanatory prose

Fields such as source relationships, source-author endorsement, relationships
to other formalizations, and automation methods use small canonical
vocabularies. These values are intended to remain machine-readable: choose the
closest category, using `other` when none applies. Put the exact nuance in the
adjacent `note`, `tool_setup`, `prompting_notes`, or automation `notes` field.
This preserves both reliable indexing and the project's own description.

## Classification

`classification` is optional, and records what the formalized result is *about*: arXiv categories and MSC2020 codes for the mathematics rather than for the source document. Every other field identifies a project by its name, its authors, or its sources, so this is the only one that lets a reader find a formalization by subject, or ask what has been formalized in a given area.

List as many identifiers of each kind as genuinely apply, or omit either list. No limit is placed on how many may appear, and no check is made that a code exists. Indexes and registries that read this file will have their own rules about how many subjects they accept and which version of each vocabulary they recognise; those are their rules rather than this standard's.

## Validating

The template carries a `# yaml-language-server: $schema=…` line, so editors with the YAML extension validate it live as you fill it in, with no setup beyond the extension.

To check it from the command line or CI (handy for agents too):

```
check-jsonschema --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json formalization.yaml
```

The schema picks the right rules from the file's `version` field; a file with no `version` is checked against the latest.
