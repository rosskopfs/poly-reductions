theory Bit_Length
  imports Main "HOL-Library.Discrete"
begin

definition bit_length :: "nat \<Rightarrow> nat" where 
"bit_length = Discrete.log"
end