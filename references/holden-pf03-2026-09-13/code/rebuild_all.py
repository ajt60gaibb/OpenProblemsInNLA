"""Regenerate every data file from the small exact inputs in build_seed.py.

This explicitly overwrites the package's generated data files. It does not
use the pre-existing algebraic seed or facet list as a construction input.
"""
from pathlib import Path
from build_seed import build_seed
from generate_cone import generate
from build_facets import build_facets
from export_matrix import export_matrix

if __name__=='__main__':
    data=Path(__file__).resolve().parent.parent/'data'
    data.mkdir(parents=True,exist_ok=True)
    build_seed(check_existing=False)
    generate()
    build_facets()
    export_matrix()
    print('All exact data files rebuilt. Run code/verify_all.py to check them.')
