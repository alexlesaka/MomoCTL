# MomoCTL 

## Content of the repository

1. \<Dir\> Dafny_Momo_CTL: Dafny files of MomoCTL used to compile java code. 
2. \<Dir\> Benchmarcs_Momo: source benchmark for momo_console.jar
3. \<Jar\> momo_console_v<version>.jar: Java runtime jar.  Please, use last version 3.3.

## Execute Momo_Console

### Main COMMAND

nohup java -Xss512m -jar momo_console.jar <directory/file path> [OPTIONAL]*

#### OPTIONAL

- /exportTable -> export a file where result-table is shown.
- /exportResults -> export a file where a model or a proof is shown.
- /tableFileName:\<filename\> -> configure the output file name where table is shown as <filename>.
- /resultsFileName:\<filename\> -> configure the output file name where results are shown as <filename>.
- /timeoutTime:\<number_of_minutes\> -> configure the timeout time. Default value: 1000 (segs)


###  Considerations when executing

Warning: If you don't use nohup and you close the session, the execution stops.

1. To see the output of the execution (if you used nohup): 
tail -f nohup.out
2. To change the output of the execution (by default nohup.out), initialize the execution with: 
nohup <command> > new_name.txt
3. To see the list of processes that are executing:
ps xa | grep java
4. To continue using the command promp while the programm is executed, writhe & at the end of the execution call: 
<command> &

### Examples
```
nohup java -Xss1G -jar momo_console.jar ./benchmarks_momo/reskill /exportTable &
nohup java -jar -Xss1G momo_console.jar ./benchmarks_momo/<path>/ /exportTable > <output_log_title>.out &  
nohup java -jar -Xss512m momo_console_3_3.jar ./benchmarks_momo/<path>/ /exportTable > <output_log_title>.out &  

nohup java -jar -Xss512m momo_console_3_3.jar ./benchmarks_momo/exp_unsat/ /exportTable > ./running_output/exp_unsat.out &
nohup java -jar -Xss512m momo_console_3_3.jar ./benchmarks_momo/exp_unsat/ /exportTable > ./running_output/exp_unsat.out & 
nohup java -jar -Xss512m momo_console_3_3.jar ./benchmarks_momo/montali_sat1/ /exportTable /tableFileName:running_output/montali_sat1_table > /montali_sat1.out &   

```
