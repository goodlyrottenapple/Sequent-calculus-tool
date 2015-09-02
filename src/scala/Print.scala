/*calc_import-BEGIN*/
import SequentCalc._
/*calc_import-END*/

object PrintCalc{
	val ASCII = "ascii"
	val LATEX = "latex"
	val ISABELLE = "isabelle"
	val ISABELLE_SE = "isabelle_se"


	def bracketIf(in:String, b: Boolean = true) : String = {
		if(b) return "(" + in + ")"
		else return in
	}

	def stringToString(x:List[Char], format:String = LATEX) : String = format match {
		case ASCII | LATEX | ISABELLE_SE => x.mkString
		case ISABELLE => "''" + x.mkString +"''"
	}

/*/*uncommentL?Structure-BEGIN*/*//*uncommentL?Structure-END*/
	def structure_listToString(in:List[Structure], format:String = LATEX) : String = "[" + in.map(x => structureToString(x, format)).mkString(", ") + "]" 
/*uncommentR?Structure-BEGIN*//*/*uncommentR?Structure-END*/*/

/*print_calc_structure-BEGIN*/
	def atpropToString(in:Atprop, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Atprop_Freevar(a) => "(" + "A?" + " " + stringToString(a, format) + ")"
				case Atpropa(a) => stringToString(a, format)
			}
		case LATEX =>
			in match {
				case Atprop_Freevar(a) => "?" + " " + stringToString(a, format)
				case Atpropa(a) => stringToString(a, format)
			}
		case ISABELLE =>
			in match {
				case Atprop_Freevar(a) => "(" + "?\\<^sub>A" + " " + stringToString(a, format) + ")"
				case Atpropa(a) => "(" + "Atprop" + " " + stringToString(a, format) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Atprop_Freevar(a) => stringToString(a, format)
				case Atpropa(a) => "(" + "Atprop" + " " + stringToString(a, format) + ")"
			}
	}

	def atpropPrec(in:Atprop) : Tuple2[Int, Int] = in match {
		case Atprop_Freevar(a) => (Int.MinValue, Int.MinValue)
		case Atpropa(a) => (Int.MinValue, Int.MinValue)
	}
	def formulaToString(in:Formula, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Formula_Un(a,b) => "(" + formula_un_opToString(a, format) + " " + formulaToString(b, format) + ")"
				case Formula_Bin(a,b,c) => "(" + formulaToString(a, format) + " " + formula_bin_opToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Freevar(a) => "(" + "F?" + " " + stringToString(a, format) + ")"
				case Formula_Atprop(a) => atpropToString(a, format)
			}
		case LATEX =>
			in match {
				case Formula_Un(a,b) => formula_un_opToString(a, format) + " " + bracketIf( formulaToString(b, format), formulaPrec(Formula_Un(a,b))._2 < formulaPrec(b)._1 )
				case Formula_Bin(a,b,c) => bracketIf( formulaToString(a, format), formulaPrec(Formula_Bin(a,b,c))._1 <= formulaPrec(a)._1 ) + " " + formula_bin_opToString(b, format) + " " + bracketIf( formulaToString(c, format), formulaPrec(Formula_Bin(a,b,c))._2 < formulaPrec(c)._1 )
				case Formula_Freevar(a) => "?_F" + " " + stringToString(a, format)
				case Formula_Atprop(a) => atpropToString(a, format)
			}
		case ISABELLE =>
			in match {
				case Formula_Un(a,b) => "(" + "U\\<^sub>F" + " " + formula_un_opToString(a, format) + " " + formulaToString(b, format) + ")"
				case Formula_Bin(a,b,c) => "(" + "B\\<^sub>F" + " " + formulaToString(a, format) + " " + formula_bin_opToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Freevar(a) => "(" + "?\\<^sub>F" + " " + stringToString(a, format) + ")"
				case Formula_Atprop(a) => "(" + atpropToString(a, format) + " " + "\\<^sub>A" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Formula_Un(a,b) => "(" + "U\\<^sub>F" + " " + formula_un_opToString(a, format) + " " + formulaToString(b, format) + ")"
				case Formula_Bin(a,b,c) => "(" + "B\\<^sub>F" + " " + formulaToString(a, format) + " " + formula_bin_opToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Freevar(a) => "(" + "?\\<^sub>F" + " " + stringToString(a, format) + ")"
				case Formula_Atprop(a) => "(" + atpropToString(a, format) + " " + "\\<^sub>A" + ")"
			}
	}

	def formulaPrec(in:Formula) : Tuple2[Int, Int] = in match {
		case Formula_Un(a,b) => a match {
			case Formula_Not() => (200, 200)
		}
		case Formula_Bin(a,b,c) => b match {
			case Formula_Or() => (400, 401)
			case Formula_ImpR() => (400, 401)
			case Formula_And() => (300, 301)
		}
		case Formula_Freevar(a) => (Int.MinValue, Int.MinValue)
		case Formula_Atprop(a) => (Int.MinValue, Int.MinValue)
	}
	def formula_bin_opToString(in:Formula_Bin_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Formula_Or() => "\\/"
				case Formula_ImpR() => ">"
				case Formula_And() => "/\\"
			}
		case LATEX =>
			in match {
				case Formula_Or() => "\\vee"
				case Formula_ImpR() => "\\rightarrow"
				case Formula_And() => "\\wedge"
			}
		case ISABELLE =>
			in match {
				case Formula_Or() => "(" + "\\<or>\\<^sub>F" + ")"
				case Formula_ImpR() => "(" + "\\<rightarrow>\\<^sub>F" + ")"
				case Formula_And() => "(" + "\\<and>\\<^sub>F" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Formula_Or() => "\\<or>\\<^sub>F"
				case Formula_ImpR() => "\\<rightarrow>\\<^sub>F"
				case Formula_And() => "\\<and>\\<^sub>F"
			}
	}

	def formula_un_opToString(in:Formula_Un_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Formula_Not() => "-"
			}
		case LATEX =>
			in match {
				case Formula_Not() => "\\lnot"
			}
		case ISABELLE =>
			in match {
				case Formula_Not() => "(" + "\\<not>\\<^sub>F" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Formula_Not() => "\\<not>\\<^sub>F"
			}
	}

	def sequentToString(in:Sequent, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Sequent_Structure(a) => structureToString(a, format)
				case Sequenta(a,b) => "(" + structureToString(a, format) + " " + "|-" + " " + structureToString(b, format) + ")"
			}
		case LATEX =>
			in match {
				case Sequent_Structure(a) => structureToString(a, format)
				case Sequenta(a,b) => structureToString(a, format) + " " + "\\vdash" + " " + structureToString(b, format)
			}
		case ISABELLE =>
			in match {
				case Sequent_Structure(a) => "(" + "Sequent_Structure" + " " + structureToString(a, format) + ")"
				case Sequenta(a,b) => "(" + structureToString(a, format) + " " + "\\<turnstile>\\<^sub>S" + " " + structureToString(b, format) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Sequent_Structure(a) => "(" + "Sequent_Structure" + " " + structureToString(a, format) + ")"
				case Sequenta(a,b) => "(" + structureToString(a, format) + " " + "\\<turnstile>\\<^sub>S" + " " + structureToString(b, format) + ")"
			}
	}

	def sequentPrec(in:Sequent) : Tuple2[Int, Int] = in match {
		case Sequent_Structure(a) => (Int.MinValue, Int.MinValue)
		case Sequenta(a,b) => (Int.MinValue, Int.MinValue)
	}
	def structureToString(in:Structure, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Structure_Formula(a) => formulaToString(a, format)
				case Structure_Zer(a) => structure_zer_opToString(a, format)
				case Structure_Freevar(a) => "(" + "?" + " " + stringToString(a, format) + ")"
				case Structure_Bin(a,b,c) => "(" + structureToString(a, format) + " " + structure_bin_opToString(b, format) + " " + structureToString(c, format) + ")"
			}
		case LATEX =>
			in match {
				case Structure_Formula(a) => formulaToString(a, format)
				case Structure_Zer(a) => structure_zer_opToString(a, format)
				case Structure_Freevar(a) => "?" + " " + stringToString(a, format)
				case Structure_Bin(a,b,c) => bracketIf( structureToString(a, format), structurePrec(Structure_Bin(a,b,c))._1 <= structurePrec(a)._1 ) + " " + structure_bin_opToString(b, format) + " " + bracketIf( structureToString(c, format), structurePrec(Structure_Bin(a,b,c))._2 < structurePrec(c)._1 )
			}
		case ISABELLE =>
			in match {
				case Structure_Formula(a) => "(" + formulaToString(a, format) + " " + "\\<^sub>S" + ")"
				case Structure_Zer(a) => "(" + "Z\\<^sub>S" + " " + structure_zer_opToString(a, format) + ")"
				case Structure_Freevar(a) => "(" + "?\\<^sub>S" + " " + stringToString(a, format) + ")"
				case Structure_Bin(a,b,c) => "(" + "B\\<^sub>S" + " " + structureToString(a, format) + " " + structure_bin_opToString(b, format) + " " + structureToString(c, format) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Structure_Formula(a) => "(" + formulaToString(a, format) + " " + "\\<^sub>S" + ")"
				case Structure_Zer(a) => "(" + "Z\\<^sub>S" + " " + structure_zer_opToString(a, format) + ")"
				case Structure_Freevar(a) => "(" + "?\\<^sub>S" + " " + stringToString(a, format) + ")"
				case Structure_Bin(a,b,c) => "(" + "B\\<^sub>S" + " " + structureToString(a, format) + " " + structure_bin_opToString(b, format) + " " + structureToString(c, format) + ")"
			}
	}

	def structurePrec(in:Structure) : Tuple2[Int, Int] = in match {
		case Structure_Formula(a) => (Int.MinValue, Int.MinValue)
		case Structure_Zer(a) => (Int.MinValue, Int.MinValue)
		case Structure_Freevar(a) => (Int.MinValue, Int.MinValue)
		case Structure_Bin(a,b,c) => b match {
			case Structure_Comma() => (500, 501)
		}
	}
	def structure_bin_opToString(in:Structure_Bin_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Structure_Comma() => ","
			}
		case LATEX =>
			in match {
				case Structure_Comma() => ","
			}
		case ISABELLE =>
			in match {
				case Structure_Comma() => "(" + ",\\<^sub>S" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Structure_Comma() => ",\\<^sub>S"
			}
	}

	def structure_zer_opToString(in:Structure_Zer_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Structure_Empty() => "I"
			}
		case LATEX =>
			in match {
				case Structure_Empty() => "I"
			}
		case ISABELLE =>
			in match {
				case Structure_Empty() => "(" + "I" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Structure_Empty() => "I"
			}
	}

/*print_calc_structure-END*/

/*print_calc_structure_rules-BEGIN*/
	def rulecutToString(in:RuleCut, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case SingleCut() => "Cut"
			}
		case LATEX =>
			in match {
				case SingleCut() => "Cut"
			}
		case ISABELLE =>
			in match {
				case SingleCut() => "(" + "SingleCut" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case SingleCut() => "SingleCut"
			}
	}

	def rulelToString(in:RuleL, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Not_L() => "Not_L"
				case And_L_1() => "And_L_1"
				case And_L_2() => "And_L_2"
				case ImpR_R() => "ImpR_R"
				case Or_L() => "Or_L"
				case Not_R() => "Not_R"
				case ImpR_L() => "ImpR_L"
				case And_R() => "And_R"
				case Or_R_2() => "Or_R_2"
				case Or_R_1() => "Or_R_1"
			}
		case LATEX =>
			in match {
				case Not_L() => "\\neg" + " " + "L"
				case And_L_1() => "\\wedge" + " " + "L_1"
				case And_L_2() => "\\wedge" + " " + "L_2"
				case ImpR_R() => "\\rightarrow" + " " + "R"
				case Or_L() => "\\vee" + " " + "L"
				case Not_R() => "\\neg" + " " + "R"
				case ImpR_L() => "\\rightarrow" + " " + "L"
				case And_R() => "\\wedge" + " " + "R"
				case Or_R_2() => "\\vee" + " " + "R_2"
				case Or_R_1() => "\\vee" + " " + "R_1"
			}
		case ISABELLE =>
			in match {
				case Not_L() => "(" + "Not_L" + ")"
				case And_L_1() => "(" + "And_L_1" + ")"
				case And_L_2() => "(" + "And_L_2" + ")"
				case ImpR_R() => "(" + "ImpR_R" + ")"
				case Or_L() => "(" + "Or_L" + ")"
				case Not_R() => "(" + "Not_R" + ")"
				case ImpR_L() => "(" + "ImpR_L" + ")"
				case And_R() => "(" + "And_R" + ")"
				case Or_R_2() => "(" + "Or_R_2" + ")"
				case Or_R_1() => "(" + "Or_R_1" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Not_L() => "Not_L"
				case And_L_1() => "And_L_1"
				case And_L_2() => "And_L_2"
				case ImpR_R() => "ImpR_R"
				case Or_L() => "Or_L"
				case Not_R() => "Not_R"
				case ImpR_L() => "ImpR_L"
				case And_R() => "And_R"
				case Or_R_2() => "Or_R_2"
				case Or_R_1() => "Or_R_1"
			}
	}

	def rulestructToString(in:RuleStruct, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case W_L() => "W_L"
				case P_L() => "P_L"
				case I_R_R2() => "I_R_R2"
				case A_R2() => "A_R2"
				case A_R() => "A_R"
				case I_R_L() => "I_R_L"
				case I_L_L2() => "I_L_L2"
				case I_L_R() => "I_L_R"
				case C_L() => "C_L"
				case C_R() => "C_R"
				case I_L_L() => "I_L_L"
				case I_R_R() => "I_R_R"
				case I_L_R2() => "I_L_R2"
				case A_L() => "A_L"
				case P_R() => "P_R"
				case I_R_L2() => "I_R_L2"
				case A_L2() => "A_L2"
				case W_R() => "W_R"
			}
		case LATEX =>
			in match {
				case W_L() => "WL"
				case P_L() => "PL"
				case I_R_R2() => "IR_R"
				case A_R2() => "AR"
				case A_R() => "AR"
				case I_R_L() => "IR_L"
				case I_L_L2() => "IL_L"
				case I_L_R() => "IL_R"
				case C_L() => "CL"
				case C_R() => "CR"
				case I_L_L() => "IL_L"
				case I_R_R() => "IR_R"
				case I_L_R2() => "IL_R"
				case A_L() => "AL"
				case P_R() => "PR"
				case I_R_L2() => "IR_L"
				case A_L2() => "AL"
				case W_R() => "WR"
			}
		case ISABELLE =>
			in match {
				case W_L() => "(" + "W_L" + ")"
				case P_L() => "(" + "P_L" + ")"
				case I_R_R2() => "(" + "I_R_R2" + ")"
				case A_R2() => "(" + "A_R2" + ")"
				case A_R() => "(" + "A_R" + ")"
				case I_R_L() => "(" + "I_R_L" + ")"
				case I_L_L2() => "(" + "I_L_L2" + ")"
				case I_L_R() => "(" + "I_L_R" + ")"
				case C_L() => "(" + "C_L" + ")"
				case C_R() => "(" + "C_R" + ")"
				case I_L_L() => "(" + "I_L_L" + ")"
				case I_R_R() => "(" + "I_R_R" + ")"
				case I_L_R2() => "(" + "I_L_R2" + ")"
				case A_L() => "(" + "A_L" + ")"
				case P_R() => "(" + "P_R" + ")"
				case I_R_L2() => "(" + "I_R_L2" + ")"
				case A_L2() => "(" + "A_L2" + ")"
				case W_R() => "(" + "W_R" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case W_L() => "W_L"
				case P_L() => "P_L"
				case I_R_R2() => "I_R_R2"
				case A_R2() => "A_R2"
				case A_R() => "A_R"
				case I_R_L() => "I_R_L"
				case I_L_L2() => "I_L_L2"
				case I_L_R() => "I_L_R"
				case C_L() => "C_L"
				case C_R() => "C_R"
				case I_L_L() => "I_L_L"
				case I_R_R() => "I_R_R"
				case I_L_R2() => "I_L_R2"
				case A_L() => "A_L"
				case P_R() => "P_R"
				case I_R_L2() => "I_R_L2"
				case A_L2() => "A_L2"
				case W_R() => "W_R"
			}
	}

	def rulezerToString(in:RuleZer, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Prem() => "Prem"
				case Partial() => "Partial"
				case Id() => "Id"
			}
		case LATEX =>
			in match {
				case Prem() => "Prem"
				case Partial() => "Partial"
				case Id() => "Id"
			}
		case ISABELLE =>
			in match {
				case Prem() => "(" + "Prem" + ")"
				case Partial() => "(" + "Partial" + ")"
				case Id() => "(" + "Id" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Prem() => "Prem"
				case Partial() => "Partial"
				case Id() => "Id"
			}
	}

	def ruleToString(in:Rule, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
             case RuleCuta(a) => rulecutToString(a, format)
             case RuleLa(a) => rulelToString(a, format)
             case RuleStructa(a) => rulestructToString(a, format)
             case RuleZera(a) => rulezerToString(a, format)
             case RuleMacro(a, pt) => rulemacroToString(a, pt, format)
			}
		case LATEX | ISABELLE_SE =>
			in match {
             case RuleCuta(a) => rulecutToString(a, format)
             case RuleLa(a) => rulelToString(a, format)
             case RuleStructa(a) => rulestructToString(a, format)
             case RuleZera(a) => rulezerToString(a, format)
             case RuleMacro(a, pt) => rulemacroToString(a, pt, format)
			}
		case ISABELLE =>
			in match {
             case RuleCuta(a) => "(" + "RuleCut" + " " + rulecutToString(a, format) + ")"
             case RuleLa(a) => "(" + "RuleL" + " " + rulelToString(a, format) + ")"
             case RuleStructa(a) => "(" + "RuleStruct" + " " + rulestructToString(a, format) + ")"
             case RuleZera(a) => "(" + "RuleZer" + " " + rulezerToString(a, format) + ")"
             case RuleMacro(a, pt) => rulemacroToString(a, pt, format)
			}
	}

/*print_calc_structure_rules-END*/

/*/*uncommentL?core_compiled-BEGIN*/*//*uncommentL?core_compiled-END*/
	def rulemacroToString(a : List[Char], pt : Prooftree, format : String = LATEX) : String = format match { 
		case ASCII => "Macro " + stringToString(a, format) + prooftreeToString(pt, format)
		case ISABELLE => "(RuleMacro " + stringToString(a, format) + prooftreeToString(pt, format) + ")"
		case LATEX => "Macro/" + stringToString(a, format)
	}

	def sequentToLatexString(seq:Sequent) = sequentToString(seq, LATEX)

	def prooftreeListToString(in:List[Prooftree], format:String = LATEX, sequentLatexPrint: Sequent => String = sequentToLatexString) : String = format match {
		case ASCII | ISABELLE => "[" + in.map(x => prooftreeToString(x, format, sequentLatexPrint)).mkString(", ") + "]"
		case LATEX => in.map(x => prooftreeToString(x, format, sequentLatexPrint)).mkString("\n")
		case ISABELLE_SE => in.map(x => prooftreeToString(x, format)).mkString("\n")
	}


	def prooftreeToString(in:Prooftree, format:String = LATEX, sequentLatexPrint: Sequent => String = sequentToLatexString) : String = format match {
		case ASCII =>
			in match {
				case Prooftreea(a,b,c) => "(" + sequentToString(a, format) + " " + "<==" + " (" + ruleToString(b, format) + ") " + prooftreeListToString(c, format, sequentLatexPrint) + ")"
			}
		case LATEX =>
			in match {
				case Prooftreea(a,b,List()) => "\\RightLabel{ $" + ruleToString(b) + "$ }\n\\AxiomC{$ " + sequentLatexPrint(a)  + " $}"
				case Prooftreea(a,b,List(c)) => prooftreeToString(c, format, sequentLatexPrint) + "\\RightLabel{ $" + ruleToString(b) + "$ }\n\\UnaryInfC{$ " + sequentLatexPrint(a)  + " $}"
				case Prooftreea(a,b,List(c, d)) => prooftreeListToString(List(c, d), format, sequentLatexPrint) + "\\RightLabel{ $" + ruleToString(b) + "$ }\n\\BinaryInfC{$ " + sequentLatexPrint(a)  + " $}"
				case Prooftreea(a,b,List(c, d, e)) => prooftreeListToString(List(c, d, e), format, sequentLatexPrint) + "\\TrinaryInfC{$ " + sequentLatexPrint(a)  + " $}\n"
				case Prooftreea(a,b,List(c, d, e, f)) => prooftreeListToString(List(c, d, e, f), format, sequentLatexPrint) + "\\QuaternaryInfC{$ " + sequentLatexPrint(a)  + " $}\n"
				case Prooftreea(a,b,list) => prooftreeListToString(list, format, sequentLatexPrint) + "\\QuinaryInfC{$ " + sequentLatexPrint(a)  + " $}\n"
			}
		case ISABELLE =>
			in match {
				case Prooftreea(a,b,c) => "(" + sequentToString(a, format) + " " + "\\<Longleftarrow>" + " " + "PT" + " " + ruleToString(b, format) + " " + prooftreeListToString(c, format, sequentLatexPrint) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Prooftreea(a,b,c) => "apply (rule_tac derivable." + ruleToString(b, format) + ")\n" + prooftreeListToString(c, format, sequentLatexPrint)
			}
	}
	
	/*def printCalcDef() : String = {
		val buf_Zer = scala.collection.mutable.ListBuffer.empty[String]
		val buf_U = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Op = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Disp = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Bin = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Cut = scala.collection.mutable.ListBuffer.empty[String]

		for (r <- ruleList) {

			val loc = List(RelAKA((x => y => z => true)))
			val ret = prooftreeToString(Prooftreea(fst(rule(loc, r)), r, snd(rule(loc, r))))
			// val ant = fst(rule(r))
			// val cons = snd(rule(r))
			// ret ++= "$" + ruleToString(r) + "$\n"
			// if(cons.length == 1){
			// 	ret ++= "\\AxiomC{$ " + sequentToString(cons(0), LATEX) + " $}\n"
			// 	ret ++= "\\UnaryInfC{$ " + sequentToString(ant, LATEX) + " $}\n"
			// }
			// else if(cons.length == 2){
			// 	ret ++= "\\AxiomC{$ " + sequentToString(cons(0), LATEX) + " $}\n"
			// 	ret ++= "\\AxiomC{$ " + sequentToString(cons(1), LATEX) + " $}\n"
			// 	ret ++= "\\BinaryInfC{$ " + sequentToString(ant, LATEX) + " $}\n"
			// }
			// else{
			// 	ret ++= "\\AxiomC{$ " + sequentToString(ant, LATEX) + " $}\n"
			// }
			// ret ++= "\n\\end{prooftree}"
			buf_Zer += ret
			// r match {
		 //        case RuleBina(a) => buf_Bin += ret.toString
		 //        case RuleCuta(a) => buf_Cut += ret.toString
		 //        case RuleDispa(a) => buf_Disp += ret.toString
		 //        case RuleOpa(a) => buf_Op += ret.toString
		 //        case RuleUa(a) => buf_U += ret.toString
		 //        case RuleZera(a) => buf_Zer += ret.toString
			// }
		}
		return "\\subsection{Zer Rules}\n" + buf_Zer.toList.mkString("\n") /*+
				"\\subsection{Unary Rules}\n" + buf_U.toList.mkString("\n") +
				"\\subsection{Display Rules}\n" + buf_Disp.toList.mkString("\n") +
				"\\subsection{Operational Rules}\n" + buf_Op.toList.mkString("\n") +
				"\\subsection{Binary Rules}\n" + buf_Bin.toList.mkString("\n") +
				"\\subsection{Cut Rules}\n" + buf_Cut.toList.mkString("\n")*/

	}
*/
/*uncommentR?core_compiled-BEGIN*//*/*uncommentR?core_compiled-END*/*/
}
