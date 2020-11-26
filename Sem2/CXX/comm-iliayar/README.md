# comm command line utility

comm -- select or reject lines common to two files

The comm utility reads file1 and file2, which should be sorted lexically, and produces three text columns as output: lines only in file1;
lines only in file2; and lines in both files.

The filename `-` means the standard input.

```bash
comm [OPTION] FILE1 FILE2
```

options:
* `-1` - suppress column 1 (lines unique to FILE1)
* `-2` - suppress column 2 (lines unique to FILE2)
* `-3` - suppress column 3 (lines that appear in both files)

### Example
```bash
$ cat e_1.txt 
AAA
BBB
CCC
$ cat e_2.txt 
AAA
CCC
EEE
$ comm e_1.txt e_2.txt 
		AAA
BBB
		CCC
	EEE
$ comm -12 e_1.txt e_2.txt 
AAA
CCC
```
