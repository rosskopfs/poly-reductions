\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_State_Seq
  imports
    ML_State
begin

ML\<open>
  structure State_Seq = State(structure M = Seq_Monad_Base; structure S = Pair_State_Result_Base)
  structure State_Stack_Seq = State_Stack(State_Seq)

  infix 1 State_Seq_THEN
  fun stsq State_Seq_THEN ifstsq = State_Seq.bind stsq (State_Seq.State o ifstsq)

  infix 1 Seq_THEN
  fun fs1 Seq_THEN fs2 = Seq.THEN (fs1, fs2)
\<close>

end