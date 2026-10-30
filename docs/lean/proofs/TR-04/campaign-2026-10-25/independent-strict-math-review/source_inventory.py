import re

def without_comments(text):
    """Strip nested Lean block comments and line comments, retaining line numbers."""
    result = []
    depth = 0
    for line in text.splitlines():
        clean = []
        i = 0
        while i < len(line):
            pair = line[i:i + 2]
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/' and depth:
                depth -= 1
                i += 2
            elif pair == '--' and (not depth):
                break
            else:
                if not depth:
                    clean.append(line[i])
                i += 1
        result.append(''.join(clean))
    if depth:
        raise RuntimeError('Unclosed source comment')
    return '\n'.join(result)

def declarations_of(name, data):
    """Track namespace components and named sections, not just a fixed prefix."""
    scopes = []
    declarations = []
    for number, line in enumerate(without_comments(data.decode()).splitlines(), 1):
        if line.startswith('namespace '):
            for part in line.split()[1].split('.'):
                scopes.append(('namespace', part))
        elif re.match('^(?:noncomputable\\s+)?section(?:\\s|$)', line):
            section_parts = re.sub('^noncomputable\\s+', '', line).split()
            scopes.append(('section', section_parts[1] if len(section_parts) > 1 else ''))
        elif re.match('^end(?:\\s|$)', line):
            parts = line.split()[1:]
            count = len(parts[0].split('.')) if parts else 1
            for _ in range(count):
                if not scopes:
                    raise RuntimeError(f'Unbalanced scope at {name}:{number}')
                scopes.pop()
        match = re.match("^(?:@\\[[^\\n]*\\]\\s*)?(?:local\\s+)?(?P<private>private\\s+)?(?:noncomputable\\s+)?(theorem|lemma|def|abbrev|instance|inductive|structure|opaque|axiom)\\s+([A-Za-z_][A-Za-z0-9_.']*)", line.lstrip())
        if match:
            private, kind, declaration = match.groups()
            prefix = '.'.join((part for kind, part in scopes if kind == 'namespace'))
            declarations.append({'name': prefix + '.' + declaration, 'kind': kind, 'source': name, 'line': number, 'visibility': 'private' if private else 'local' if line.startswith('local ') else 'public'})
            if private and kind not in {'theorem', 'lemma', 'def', 'abbrev'}:
                raise RuntimeError('Private non-theorem requires an explicit audit implementation: ' + name)
        if re.match('^protected\\s+', line):
            raise RuntimeError('Unsupported declaration modifier requires explicit audit: ' + name)
    if any((kind == 'namespace' for kind, _ in scopes)):
        raise RuntimeError('Unclosed namespace: ' + name)
    return declarations
