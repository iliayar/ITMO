#!/usr/bin/env python3
import json
import sys

def main():
    inp = sys.stdin.read()
    data = json.loads(inp)

    j = 2
    for note in data:
        print(f"Слайд {j}")
        print(note["value"])

        print()
        print("------------------------")
        print()

        j += 1

if __name__ == "__main__":
    main()
