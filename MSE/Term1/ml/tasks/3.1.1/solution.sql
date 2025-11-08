(SELECT salary, 21 as ord FROM ROSSTAT_SALARY_RU 
	WHERE region_name!='Республика Татарстан'
		AND region_name!='Республика Марий Эл'
	ORDER BY salary OFFSET 20 LIMIT 1)
UNION
(SELECT salary, 22 as ord FROM ROSSTAT_SALARY_RU 
	WHERE region_name!='Республика Татарстан'
		AND region_name!='Республика Марий Эл'
	ORDER BY salary OFFSET 21 LIMIT 1)
UNION
(SELECT salary, 77 as ord FROM ROSSTAT_SALARY_RU 
	WHERE region_name!='Республика Татарстан'
		AND region_name!='Республика Марий Эл'
	ORDER BY salary OFFSET 76 LIMIT 1);

SELECT avg(salary) as avg FROM ROSSTAT_SALARY_RU 
	WHERE region_name!='Республика Татарстан'
		AND region_name!='Республика Марий Эл';

SELECT salary FROM ROSSTAT_SALARY_RU
	ORDER BY salary OFFSET
		(SELECT count(*) FROM ROSSTAT_SALARY_RU 
			WHERE region_name!='Республика Татарстан'
				AND region_name!='Республика Марий Эл') / 2
		LIMIT 2;
