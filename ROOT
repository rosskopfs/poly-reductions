chapter Poly_Reductions

session Poly_Reductions_Base = HOL +
  sessions
    NREST
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

session Karp21 in Karp21 = Poly_Reductions_Lib +
  sessions
    "HOL-Real_Asymp"
    Landau_Symbols
    NREST
  directories
    CNF_SAT_To_Clique
    CNF_SAT_To_TC
    HC_To_UHC
    TC_To_ChrN
    VC_Set_To_VC_List
    VC_To_FNS
    VC_To_HC
  theories
    All_Reductions_Poly

session IMP_Minus in "IMP-" = "HOL-Eisbach" +
  theories
    Com
    Big_StepT
    Small_StepT
    Big_Step_Small_Step_Equivalence

session Cook_Levin_IMP in Cook_Levin_IMP = "HOL-Analysis" +
  sessions
    Poly_Reductions_Lib
    IMP_Minus
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