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

session IMP_Minus_Views in "Cook_Levin_IMP/Views" = IMP_Minus +
  sessions
    "HOL-Library"
  directories
    "ML_Typeclasses"
    "ML_Typeclasses/State"
  theories
    "Views_Cook_Levin"

session IMP_Minus_Views_Examples in "Cook_Levin_IMP/Views/Examples" = Cook_Levin_IMP +
  theories
    "Elemof"
    "Filter_Defined_Acc"

session Cook_Levin_IMP in Cook_Levin_IMP = "HOL-Analysis" +
  sessions
    Poly_Reductions_Lib
    IMP_Minus
    IMP_Minus_Views
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
