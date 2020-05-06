#!/usr/bin/python3

import datetime

HEADER="""
// Generated at %s 
// By iliayar
""" % datetime.datetime.now()

TEMPLATE_FILE="template.cpp"
SOLUTION_FILE="sol.cpp"
TASK_FILE="task.cpp"

CODE_LINE= "CODE_HERE"


template = open(TEMPLATE_FILE)
solution = open(SOLUTION_FILE)

task = open(TASK_FILE, 'w')

task.write(HEADER)

for template_line in template.readlines():
    if CODE_LINE in template_line:
        task.write("//##################CODE BEGIN#############")
        for sol_line in solution.readlines()[1:]:
            task.write(sol_line)
        task.write("//##################CODE END###############")
        continue
    task.write(template_line)

template.close()
solution.close()
task.close()
