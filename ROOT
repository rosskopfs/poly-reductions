chapter Poly_Reductions

session Poly_Reductions_Base = HOL +
  sessions
    "HOL-Real_Asymp"
    Landau_Symbols

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
    "Auxiliaries/Graph_Auxiliaries"
    "Graph_Extensions/Vwalk_Cycle"
    Polynomial_Growth_Functions
    SAT_Definition

session IMP_Minus in "IMP-" = "HOL-Eisbach" +
  theories
    Com
    Big_StepT
    Small_StepT
    Big_Step_Small_Step_Equivalence
    IMP_Tailcalls_Dynamic

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

session HOL_To_HOL_Nat in "HOL_To_IMP_Minus/HOL_To_HOL_Nat" = Transport +
  sessions
    "HOL-Library"
    "ML_Unification"
  theories
    HOL_To_HOL_Nat_Base

session HOL_Nat_To_IMP_Minus in "HOL_To_IMP_Minus/HOL_Nat_To_IMP_Minus" = IMP_Minus +
  sessions
    HOL_To_HOL_Nat
    ML_Unification
  directories
    "Automation"
    "Compile_HOL_Nat_To_IMP"
    "States"
  theories
    HOL_Nat_To_IMP_Tactics

session HOL_To_IMP_Minus in "HOL_To_IMP_Minus" = HOL_Nat_To_IMP_Minus +
  directories
    "Refinements"
  theories
    HOL_To_IMP_Minus_Arithmetics

session Cook_Levin_IMP in Cook_Levin_IMP = "HOL-Analysis" +
  sessions
    Poly_Reductions_Lib
    HOL_To_IMP_Minus
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
    Cook_Levin
    IMP_Minus_To_SAS_Plus
    Primitives_IMP_Minus
    IMP_Minus_To_IMP_Minus_Minus_State_Translations_IMP
    Binary_Arithmetic_IMP
