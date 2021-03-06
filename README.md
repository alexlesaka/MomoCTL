# MomoCTL 

## Content of the repository

1. \<Dir\> Dafny_MomoCTL_3_3: Dafny files of MomoCTL used to compile java code for momo_console_3_3.jar. 
2. \<Dir\> Dafny_MomoCTL_3_4: Dafny files of MomoCTL used to compile java code for momo_console_3_4.jar. 
3. \<Dir\> Benchmarcs_Momo.zip: source benchmarks for momoCTL.
4. \<Jar\> momo_console_3_3.jar: Java runtime jar 
5. \<Jar\> momo_console_3_4.jar: Java runtime jar (last version 3.4).

## Execute Momo_Console

### Main COMMAND

nohup java -Xss512m -jar momo_console_<version>.jar <directory/file path> [OPTIONAL]*

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
nohup java -Xss1G -jar momo_console_3_3.jar ./benchmarks_Momo/reskill /exportTable &
nohup java -jar -Xss1G momo_console_3_3.jar ./benchmarks_Momo/<path>/ /exportTable > <output_log_title>.out &  
nohup java -jar -Xss512m momo_console_3_3.jar ./benchmarks_Momo/<path>/ /exportTable > <output_log_title>.out &  

nohup java -jar -Xss512m momo_console_3_3.jar ./benchmarks_Momo/exp_unsat/ /exportTable > ./running_output/exp_unsat.out &
nohup java -jar -Xss512m momo_console_3_3.jar ./benchmarks_Momo/exp_unsat/ /exportTable > ./running_output/exp_unsat.out & 
nohup java -jar -Xss512m momo_console_3_3.jar ./benchmarks_Momo/montali_sat1/ /exportTable /tableFileName:running_output/montali_sat1_table > /montali_sat1.out &   

```
 
### Models and Proofs
java -jar -Xss512m momo_console_3_3.jar file-address

### Example of model: busproc1.ctl
![busproc1-model](https://user-images.githubusercontent.com/23459019/161607179-d1466e93-1c96-49cd-b2f4-0331550775a6.JPG)
 
 ### Example of small-step proof: step_induction.2.ctl
 ![step_induction 2-Proof](https://user-images.githubusercontent.com/23459019/161727561-e727a597-aaf1-460d-a032-3bf3e71b4056.JPG)
 


 
