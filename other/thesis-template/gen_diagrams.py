#!/usr/bin/env python3

import json
import sys
import pathlib

FIGURES = pathlib.Path('./.figures')

def main():
    fig_type = sys.argv[1]
    fig_type_path = FIGURES / fig_type

    if not fig_type_path.exists():
        fig_type_path.mkdir(parents=True)

    inp = sys.stdin.read()
    data = json.loads(inp)

    figures = set()

    for meta in data:
        format, name, content = meta['value']

        filename = f'{name}.{format}'
        figures.add(filename)

        path = fig_type_path / filename
        print(f'Writing diagram {name} to {path}')

        with path.open('w') as f:
            f.write(content)

    for entry in fig_type_path.iterdir():
        if entry.name not in figures:
            entry.unlink()

if __name__ == "__main__":
    main()
