chapter Poly_Reductions

session Expressions in "Expressions" = HOL +
  directories
    Basics
    Global_Calls
    Plus_Minus
    Refinements
    "Refinements/Assign_Pure"
    Tail_Calls
    Whiles
  theories
    Expression_Tail_Call_Whiles_Plus_Minus

session IMP_Minus in "IMP-" = "HOL-Eisbach" +
  theories
    Com
    Big_StepT
    Small_StepT
    Big_Step_Small_Step_Equivalence
    IMP_Tailcalls_Dynamic

session HOL_To_HOL_Nat in "HOL_To_IMP_Minus/HOL_To_HOL_Nat" = Transport +
  sessions
    "HOL-Library"
  theories
    HOL_To_HOL_Nat_Basics
    HOL_To_HOL_Nat_Tests

session HOL_Nat_To_IMP_Minus in "HOL_To_IMP_Minus/HOL_Nat_To_IMP_Minus" = IMP_Minus +
  sessions
    HOL_To_HOL_Nat
    ML_Typeclasses
    ML_Unification
  directories
    "Automation"
    "Compile_HOL_Nat_To_IMP"
    "States"
  theories
   "Automation/HOL_Nat_To_IMP_Tactics"

session HOL_To_IMP_Minus in "HOL_To_IMP_Minus" = HOL_Nat_To_IMP_Minus +
  directories
    "Refinements"
  theories
    HOL_To_IMP_Minus_Arithmetics

session Poly_Reductions_Lib in Lib = "HOL-Analysis" +
  sessions
    "HOL-Real_Asymp"
    Landau_Symbols
    Graph_Theory
    Transport
  directories
    Auxiliaries
    Graph_Extensions
  theories
    Graph_Auxiliaries
    Vwalk_Cycle
    Polynomial_Growth_Functions
    SAT_Definition_List
    SAT_Definition
    Tail_Rec_Funs

session Complexity_Basics in "Cook_Levin_IMP/Complexity_Classes" = Poly_Reductions_Lib +
  sessions
    IMP_Minus
  theories
    Cook_Levin

session "IMP-_To_SAS+_HOL" in "Cook_Levin_IMP/IMP-_To_SAS+/IMP-_To_SAS+_HOL" = "HOL-Analysis" +
  sessions
    Verified_SAT_Based_AI_Planning
    Complexity_Basics
  directories
    "IMP-_To_IMP--"
    "IMP--_To_SAS++"
    "SAS++_To_SAS+"
  theories
    "IMP_Minus_To_SAS_Plus"
    "IMP_Minus_To_SAT"

(*The following two sessions need to be redone using the automation*)

(*
session "IMP-_To_SAS+_Nat" in "Cook_Levin_IMP/IMP-_To_SAS+/IMP-_To_SAS+_Nat" = "HOL-Analysis" +
  sessions
    "IMP-_To_SAS+_HOL"
  directories
    "IMP-_To_IMP--"
    "IMP--_To_SAS++"
    "SAS++_To_SAS+"
  theories
    "IMP_Minus_To_SAS_Plus_Nat"
    "IMP_Minus_To_SAT_Nat"

session "IMP-_To_SAS+_IMP_Minus" in "Cook_Levin_IMP/IMP-_To_SAS+/IMP-_To_SAS+_IMP_Minus" = "HOL-Analysis" +
  sessions
    "IMP-_To_SAS+_Nat"
  directories
    "IMP-_To_IMP--"
    "IMP--_To_SAS++"
    "SAS++_To_SAS+"
  theories
    "Primitives_IMP_Minus"
    "Binary_Operations_IMP_Minus"
    "Binary_Arithmetic_IMP_Minus"
    "IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP_Minus"
*)
(*session Cook_Levin_IMP in Cook_Levin_IMP = "HOL-Analysis" +
  sessions
    Poly_Reductions_Lib
    (*HOL_To_IMP_Minus*)
    "IMP_Minus"
    "HOL-Real_Asymp"
    Landau_Symbols
    Verified_SAT_Based_AI_Planning
    Akra_Bazzi
  directories
    Complexity_classes
    "IMP-_To_SAS+"
    "IMP-_To_SAS+/IMP-_To_IMP--"
    "IMP-_To_SAS+/IMP--_To_SAS++"
    "IMP-_To_SAS+/SAS++_To_SAS+"
  theories
    "Complexity_classes/Cook_Levin"
    "IMP-_To_SAS+/IMP_Minus_To_SAS_Plus"
    "IMP-_To_SAS+/IMP-_To_IMP--/Primitives_IMP_Minus"
    "IMP-_To_SAS+/IMP-_To_IMP--/IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP"
    "IMP-_To_SAS+/IMP-_To_IMP--/Binary_Arithmetic_IMP"*)