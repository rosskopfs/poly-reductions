text \<open>Here are some examples that might help with understanding of the TM from Cook_Levin\<close>

theory TM_Playground
  imports Cook_Levin.Basics Cook_Levin.Combinations
begin

subsection \<open>Helper functions\<close>

text \<open>For a given config, print the first m symbols of n-th tape\<close>
fun print_tape :: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> symbol list" where
  "print_tape cfg n 0 = []" |
  "print_tape cfg n (Suc m) = (print_tape cfg n m) @ [(cfg <:> n) m]"

subsection \<open>Example 1: copy-paste machine\<close>

text \<open>A minimum machine that copies the 0-th (read-only) tape to the 1st tape
With only two states: q_0 and q_f
In q_0, it copies the symbol from the 0-th tape to the 1st tape,
then moves the head one step to right on both tapes, remains in state q_0, iff the symbol is not \<box>;
otherwise when then symbol from the 0-th tape is \<box>, it copies it as well to the 1st tape,
then turn to state q_f (and terminates)
\<close>

definition copy_paste_command :: command where
  "copy_paste_command = (
    \<lambda> symbols_read_from_tapes.
      (if symbols_read_from_tapes ! 0 = \<box> then 1 else 0, \<comment> \<open>new state\<close>
       [(symbols_read_from_tapes ! 0, Right), \<comment> \<open>0-th tape remains the same\<close>
        (symbols_read_from_tapes ! 0, Right)]) \<comment> \<open>copies the symbol from 0-th tape to the 1st tape\<close>
   )"

\<comment> \<open>copy_paste_command is a well-formed command for a 2-tape TM with 1 state (excluding q_f)\<close>
lemma "wf_command 2 1 copy_paste_command"
  unfolding copy_paste_command_def
  unfolding wf_command_def
  by simp


\<comment> \<open>copy_paste_command is a Turing command for a 2-tape TM with 1 state (excluding q_f),
    and with the alphabet set containing only one symbol (\<box>)\<close>
lemma "turing_command 2 1 1 copy_paste_command"
  unfolding copy_paste_command_def
  unfolding turing_command_def
  unfolding wf_command_def
  apply auto
  by (metis One_nat_def diff_Suc_1 fst_conv less_2_cases_iff nth_Cons_0 nth_Cons_numeral numerals(1))

\<comment> \<open>Same as above,
    and with the alphabet set containing only 4 symbols (\<box>, \<triangleright>, \<zero>, \<one>)\<close>
lemma cp_tm_cmd_214: "turing_command 2 1 4 copy_paste_command"
  unfolding copy_paste_command_def
  unfolding turing_command_def
  unfolding wf_command_def
  apply auto
  by (metis One_nat_def diff_Suc_1 fst_conv less_2_cases_iff nth_Cons_0 nth_Cons_numeral numerals(1))

\<comment> \<open>And so on, this works for any size of the alphabet set as long as it is not empty\<close>
thm turing_command_mono
lemma "turing_command 2 1 100 copy_paste_command"
  unfolding copy_paste_command_def
  unfolding turing_command_def
  unfolding wf_command_def
  apply auto
  by (metis One_nat_def diff_Suc_1 fst_conv less_2_cases_iff nth_Cons_0 nth_Cons_numeral numerals(1))


definition copy_paste_machine :: machine where
  "copy_paste_machine = [copy_paste_command]" \<comment> \<open>The behavior under each states except for q_f\<close>
                                              \<comment> \<open>In this case, only for q_0\<close>

\<comment> \<open>The copy-paste machine is a well-formed 2-tape TM for the alphabet set of size 4\<close>
lemma "turing_machine 2 4 copy_paste_machine"
  unfolding turing_machine_def copy_paste_machine_def
  using cp_tm_cmd_214 by auto

definition start_content :: "symbol list" where
  "start_content = string_to_symbols [\<bbbI>,\<bbbO>,\<bbbI>,\<bbbO>, \<bbbO>,\<bbbO>,\<bbbI>,\<bbbO>]" \<comment> \<open>42 in little-endian\<close>
definition start_cfg_eg :: "config" where
  "start_cfg_eg = start_config 2 start_content"
value "print_tape start_cfg_eg 0 10"
value "print_tape start_cfg_eg 1 10"

\<comment> \<open>An example of the executing of the copy-paste machine.
    Showing the first 10 symbols on the 1st tape after each of the first 12 steps.\<close>
value "print_tape (execute copy_paste_machine start_cfg_eg 0) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 1) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 2) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 3) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 4) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 5) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 6) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 7) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 8) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 9) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 10) 1 10"
value "print_tape (execute copy_paste_machine start_cfg_eg 11) 1 10"
\<comment> \<open>Same example as above, showing the position of head on tape 0 after each of the first 12 steps.\<close>
value "(execute copy_paste_machine start_cfg_eg 0) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 1) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 2) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 3) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 4) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 5) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 6) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 7) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 8) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 9) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 10) <#> 0"
value "(execute copy_paste_machine start_cfg_eg 11) <#> 0"
\<comment> \<open>Same example as above, showing the state after each of the first 12 steps.\<close>
value "fst (execute copy_paste_machine start_cfg_eg 0)"
value "fst (execute copy_paste_machine start_cfg_eg 1)"
value "fst (execute copy_paste_machine start_cfg_eg 2)"
value "fst (execute copy_paste_machine start_cfg_eg 3)"
value "fst (execute copy_paste_machine start_cfg_eg 4)"
value "fst (execute copy_paste_machine start_cfg_eg 5)"
value "fst (execute copy_paste_machine start_cfg_eg 6)"
value "fst (execute copy_paste_machine start_cfg_eg 7)"
value "fst (execute copy_paste_machine start_cfg_eg 8)"
value "fst (execute copy_paste_machine start_cfg_eg 9)"
value "fst (execute copy_paste_machine start_cfg_eg 10)"
value "fst (execute copy_paste_machine start_cfg_eg 11)"

definition end_cfg_eg :: "config" where
  "end_cfg_eg = (1, [(\<lfloor>start_content\<rfloor>, 10), (\<lfloor>start_content\<rfloor>, 10)])"
value "print_tape end_cfg_eg 0 10"
value "print_tape end_cfg_eg 1 10"

lemma "transits copy_paste_machine start_cfg_eg 12 end_cfg_eg"
  sorry (* TODO: How to prove? *)


lemma "transforms copy_paste_machine
       [(\<lfloor>start_content\<rfloor>, 0), (\<lfloor>[]\<rfloor>, 0)]
       12
       [(\<lfloor>start_content\<rfloor>, 0), (\<lfloor>start_content\<rfloor>, 0)]"
  sorry (* TODO: proof using tform *)


end