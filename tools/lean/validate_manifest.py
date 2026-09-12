#!/usr/bin/env python3
"""Validate the real v0.4 metadata schema and advertised comparator coverage.

This validates metadata consistency, not truth of a proof or a review report.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import jsonschema
import yaml

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate metadata/configuration key: {key!r}")
        result[key] = value
    return result


class UniqueSafeLoader(yaml.SafeLoader):
    def construct_mapping(self, node, deep=False):
        self.flatten_mapping(node)
        return unique_pairs((self.construct_object(key, deep=deep),
                             self.construct_object(value, deep=deep))
                            for key, value in node.value)


def validate(project: Path, schema: dict) -> None:
    metadata = yaml.load((project / "formalization.yaml").read_text(), Loader=UniqueSafeLoader)
    validator = jsonschema.validators.validator_for(schema)
    validator.check_schema(schema)
    validator(schema).validate(metadata)
    if metadata.get("version") != "v0.4":
        raise ValueError("Use the pinned v0.4 manifest schema explicitly")
    config = json.loads((project / "comparator.json").read_text(), object_pairs_hook=unique_pairs)
    names = config.get("theorem_names", [])
    if not names or len(names) != len(set(names)):
        raise ValueError("Comparator must select distinct, nonempty target declarations")
    if config.get("definition_names", []) != []:
        raise ValueError("Target definitions must not be replaceable definition holes")
    axioms = config.get("permitted_axioms", [])
    if not isinstance(axioms, list) or not set(axioms) <= ALLOWED_AXIOMS:
        raise ValueError("Comparator permits nonstandard axioms")
    status = metadata.get("status", {})
    if status.get("sorry_count") != 0 or status.get("sorry_in_definitions") != 0:
        raise ValueError("Completed project metadata must report zero proof-development sorries")
    results = status.get("main_results", [])
    declared = [r.get("declaration") for r in results]
    if set(declared) != set(names) or len(declared) != len(names):
        raise ValueError("Every advertised result must be selected exactly once by Comparator")
    if not set(status.get("axioms", [])) <= ALLOWED_AXIOMS:
        raise ValueError("Metadata reports nonstandard axioms")
    for result in results:
        if result.get("sorry_count") != 0 or not set(result.get("axioms", [])) <= ALLOWED_AXIOMS:
            raise ValueError(f"Unverified result metadata: {result.get('declaration')}")
        if result.get("comparator_config") != "comparator.json":
            raise ValueError("Every result must refer to the checked comparator.json")
        file = result.get("file", "")
        path = (project / file).resolve()
        if not file or not path.is_relative_to(project.resolve()) or not path.is_file():
            raise ValueError(f"Result source is absent or outside project: {file}")
    print(f"Manifest schema and comparator coverage: PASS ({len(names)} declarations)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    args = parser.parse_args()
    schema = Path(__file__).resolve().parents[2] / "docs/lean/schema/v0.4.schema.json"
    validate(args.project, json.loads(schema.read_text()))


if __name__ == "__main__":
    main()
