.PHONY: verify docs integrity manifest
verify:
	python3 verification/run_all.py
	python3 verification/rook_partial.py
	python3 verification/check_document_constants.py

docs:
	python3 scripts/build_documents.py

integrity:
	python3 scripts/check_integrity.py

manifest:
	python3 scripts/create_manifest.py
