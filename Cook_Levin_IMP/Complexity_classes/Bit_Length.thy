theory Bit_Length
  imports Main "HOL-Library.Discrete_Functions"
begin

definition bit_length :: "nat \<Rightarrow> nat" where
"bit_length = floor_log"
end