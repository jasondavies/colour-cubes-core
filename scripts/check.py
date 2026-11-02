#!/usr/bin/env python3
"""Guard proof sources, pinned dependencies and the public theorem axiom audit."""
from pathlib import Path
import json, re, subprocess, tomllib
root = Path(__file__).resolve().parents[1]
config = tomllib.loads((root / 'lakefile.toml').read_text())
manifest = json.loads((root / 'lake-manifest.json').read_text())
assert [d['name'] for d in config['require']] == ['mathlib']
assert all(re.fullmatch('[0-9a-f]{40}', p['rev']) for p in manifest['packages'])
for path in [root / 'ColourCubes.lean', *(root / 'ColourCubes').glob('*.lean')]:
    code = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', code), path
    assert all(m.startswith(('Mathlib', 'ColourCubes.')) for m in re.findall(r'^(?:public )?import (.+)$', code, re.M)), path
result = subprocess.run(['lake', 'env', 'lean', 'Audit.lean'], cwd=root, text=True, capture_output=True)
print(result.stdout, end='')
if result.returncode:
    raise SystemExit(result.stderr)
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout)
expected = re.findall(r'^#print axioms (.+)$', (root / 'Audit.lean').read_text(), re.M)
assert [name for name, _ in reports] == expected
assert all({a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'} for _, axioms in reports)
print(f'All {len(reports)} axiom guards passed; no paper dependencies or proof holes.')
