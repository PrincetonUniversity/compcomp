#!/bin/bash

#count no. of lines between 'Operational semantics' and EOF
# $1: file 1
# $2: file 2 (if any)

if [ ! -f $1 ]; then echo "File $1 does not exist"
else
  FILE1=`awk 'BEGIN{i=0;opsem=0}{if (opsem>0) {i++}}/Operational semantics/{opsem=1}END{print i}' $1`
  if [ -z $2 ]; then echo $FILE1  
  else 
      FILE2=`awk 'BEGIN{i=0;opsem=0}{if (opsem>0) {i++}}/Operational semantics/{opsem=1}END{print i}' $2`
      TOT=$(($FILE1+$FILE2))
      echo $TOT
  fi
fi


