import scala.util.parsing.combinator._
import scala.util.parsing.json._
/*calc_import-BEGIN*/
import SequentCalc._
/*calc_import-END*/

object Parser extends JavaTokenParsers with OperatorPrecedenceParsers {

	lazy val stringParser:PackratParser[List[Char]] = 
		ident ^^ { i => i.toList }


	def listParser[T](innerParser:PackratParser[T]):PackratParser[List[T]] =
		"[" ~ "]" ^^ { _ => List[T]() } |
		"[" ~> rep(innerParser <~ ",") ~ innerParser <~ "]" ^^ { case list ~ last => list ++ List[T](last) }

/*/*uncommentL?Structure-BEGIN*/*//*uncommentL?Structure-END*/
	lazy val structure_listParser:PackratParser[List[Structure]] = listParser[Structure](structureParser)
/*uncommentR?Structure-BEGIN*//*/*uncommentR?Structure-END*/*/

/*parser_calc_structure-BEGIN*/
	lazy val atpropParser : PackratParser[Atprop] = 
		atprop_freevarParser | atpropaParser | "(" ~> atpropParser <~ ")"

	lazy val atprop_freevarParser : PackratParser[Atprop] =
		"A?" ~ stringParser ^^ { case "A?" ~ a => Atprop_Freevar(a) }

	lazy val atpropaParser : PackratParser[Atprop] =
		stringParser ^^ { case a => Atpropa(a) }

	def parseAtprop(s:String) : Option[Atprop] = parseAll(atpropParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}





	lazy val formulaParser:PackratParser[Formula] = operators[Any,Formula](
		Prefix(200)(formula_notParser) { case (_, a) => Formula_Un(Formula_Not(), a) },
		Infix(400, 401)(formula_orParser) { (_, a, b) => Formula_Bin(a, Formula_Or(), b ) },
		Infix(400, 401)(formula_imprParser) { (_, a, b) => Formula_Bin(a, Formula_ImpR(), b ) },
		Infix(300, 301)(formula_andParser) { (_, a, b) => Formula_Bin(a, Formula_And(), b ) }
	) ( formula_freevarParser | formula_atpropParser | "(" ~> formulaParser <~ ")" )

	def parseFormula(s:String) : Option[Formula] = parseAll(formulaParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}

	lazy val formula_unParser : PackratParser[Formula] =
		formula_un_opParser ~ formulaParser ^^ { case a ~ b => Formula_Un(a, b) }

	lazy val formula_binParser : PackratParser[Formula] =
		formulaParser ~ formula_bin_opParser ~ formulaParser ^^ { case a ~ b ~ c => Formula_Bin(a, b, c) }

	lazy val formula_freevarParser : PackratParser[Formula] =
		"F?" ~ stringParser ^^ { case "F?" ~ a => Formula_Freevar(a) }

	lazy val formula_atpropParser : PackratParser[Formula] =
		atpropParser ^^ { case a => Formula_Atprop(a) }



	lazy val formula_bin_opParser : PackratParser[Formula_Bin_Op] = 
		formula_orParser | formula_imprParser | formula_andParser | "(" ~> formula_bin_opParser <~ ")"

	lazy val formula_orParser : PackratParser[Formula_Bin_Op] =
		"\\/" ^^ { _ => Formula_Or() }

	lazy val formula_imprParser : PackratParser[Formula_Bin_Op] =
		">" ^^ { _ => Formula_ImpR() }

	lazy val formula_andParser : PackratParser[Formula_Bin_Op] =
		"/\\" ^^ { _ => Formula_And() }

	def parseFormula_Bin_Op(s:String) : Option[Formula_Bin_Op] = parseAll(formula_bin_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val formula_un_opParser : PackratParser[Formula_Un_Op] = 
		formula_notParser | "(" ~> formula_un_opParser <~ ")"

	lazy val formula_notParser : PackratParser[Formula_Un_Op] =
		"-" ^^ { _ => Formula_Not() }

	def parseFormula_Un_Op(s:String) : Option[Formula_Un_Op] = parseAll(formula_un_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val sequentParser : PackratParser[Sequent] = 
		sequentaParser | "(" ~> sequentParser <~ ")"

	lazy val sequent_structureParser : PackratParser[Sequent] =
		structureParser ^^ { case a => Sequent_Structure(a) }

	lazy val sequentaParser : PackratParser[Sequent] =
		structureParser ~ "|-" ~ structureParser ^^ { case a ~ "|-" ~ b => Sequenta(a, b) }

	def parseSequent(s:String) : Option[Sequent] = parseAll(sequentParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}





	lazy val structureParser:PackratParser[Structure] = operators[Any,Structure](
		
		Infix(500, 501)(structure_commaParser) { (_, a, b) => Structure_Bin(a, Structure_Comma(), b ) }
	) ( structure_freevarParser | structure_zerParser | structure_formulaParser | "(" ~> structureParser <~ ")" )

	def parseStructure(s:String) : Option[Structure] = parseAll(structureParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}

	lazy val structure_formulaParser : PackratParser[Structure] =
		formulaParser ^^ { case a => Structure_Formula(a) }

	lazy val structure_zerParser : PackratParser[Structure] =
		structure_zer_opParser ^^ { case a => Structure_Zer(a) }

	lazy val structure_freevarParser : PackratParser[Structure] =
		"?" ~ stringParser ^^ { case "?" ~ a => Structure_Freevar(a) }

	lazy val structure_binParser : PackratParser[Structure] =
		structureParser ~ structure_bin_opParser ~ structureParser ^^ { case a ~ b ~ c => Structure_Bin(a, b, c) }



	lazy val structure_bin_opParser : PackratParser[Structure_Bin_Op] = 
		structure_commaParser | "(" ~> structure_bin_opParser <~ ")"

	lazy val structure_commaParser : PackratParser[Structure_Bin_Op] =
		"," ^^ { _ => Structure_Comma() }

	def parseStructure_Bin_Op(s:String) : Option[Structure_Bin_Op] = parseAll(structure_bin_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val structure_zer_opParser : PackratParser[Structure_Zer_Op] = 
		structure_emptyParser | "(" ~> structure_zer_opParser <~ ")"

	lazy val structure_emptyParser : PackratParser[Structure_Zer_Op] =
		"I" ^^ { _ => Structure_Empty() }

	def parseStructure_Zer_Op(s:String) : Option[Structure_Zer_Op] = parseAll(structure_zer_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}
/*parser_calc_structure-END*/

/*parser_calc_structure_rules-BEGIN*/
	lazy val rulecutParser : PackratParser[RuleCut] = 
		singlecutParser | "(" ~> rulecutParser <~ ")"

	lazy val singlecutParser : PackratParser[RuleCut] =
		"Cut" ^^ { _ => SingleCut() }

	def parseRuleCut(s:String) : Option[RuleCut] = parseAll(rulecutParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulelParser : PackratParser[RuleL] = 
		or_r_2Parser | or_r_1Parser | or_lParser | not_rParser | not_lParser | impr_rParser | impr_lParser | and_rParser | and_l_2Parser | and_l_1Parser | "(" ~> rulelParser <~ ")"

	lazy val not_lParser : PackratParser[RuleL] =
		"Not_L" ^^ { _ => Not_L() }

	lazy val and_l_1Parser : PackratParser[RuleL] =
		"And_L_1" ^^ { _ => And_L_1() }

	lazy val and_l_2Parser : PackratParser[RuleL] =
		"And_L_2" ^^ { _ => And_L_2() }

	lazy val impr_rParser : PackratParser[RuleL] =
		"ImpR_R" ^^ { _ => ImpR_R() }

	lazy val or_lParser : PackratParser[RuleL] =
		"Or_L" ^^ { _ => Or_L() }

	lazy val not_rParser : PackratParser[RuleL] =
		"Not_R" ^^ { _ => Not_R() }

	lazy val impr_lParser : PackratParser[RuleL] =
		"ImpR_L" ^^ { _ => ImpR_L() }

	lazy val and_rParser : PackratParser[RuleL] =
		"And_R" ^^ { _ => And_R() }

	lazy val or_r_2Parser : PackratParser[RuleL] =
		"Or_R_2" ^^ { _ => Or_R_2() }

	lazy val or_r_1Parser : PackratParser[RuleL] =
		"Or_R_1" ^^ { _ => Or_R_1() }

	def parseRuleL(s:String) : Option[RuleL] = parseAll(rulelParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulestructParser : PackratParser[RuleStruct] = 
		w_rParser | w_lParser | p_rParser | p_lParser | i_r_r2Parser | i_r_rParser | i_r_l2Parser | i_r_lParser | i_l_r2Parser | i_l_rParser | i_l_l2Parser | i_l_lParser | c_rParser | c_lParser | a_r2Parser | a_rParser | a_l2Parser | a_lParser | "(" ~> rulestructParser <~ ")"

	lazy val w_lParser : PackratParser[RuleStruct] =
		"W_L" ^^ { _ => W_L() }

	lazy val p_lParser : PackratParser[RuleStruct] =
		"P_L" ^^ { _ => P_L() }

	lazy val i_r_r2Parser : PackratParser[RuleStruct] =
		"I_R_R2" ^^ { _ => I_R_R2() }

	lazy val a_r2Parser : PackratParser[RuleStruct] =
		"A_R2" ^^ { _ => A_R2() }

	lazy val a_rParser : PackratParser[RuleStruct] =
		"A_R" ^^ { _ => A_R() }

	lazy val i_r_lParser : PackratParser[RuleStruct] =
		"I_R_L" ^^ { _ => I_R_L() }

	lazy val i_l_l2Parser : PackratParser[RuleStruct] =
		"I_L_L2" ^^ { _ => I_L_L2() }

	lazy val i_l_rParser : PackratParser[RuleStruct] =
		"I_L_R" ^^ { _ => I_L_R() }

	lazy val c_lParser : PackratParser[RuleStruct] =
		"C_L" ^^ { _ => C_L() }

	lazy val c_rParser : PackratParser[RuleStruct] =
		"C_R" ^^ { _ => C_R() }

	lazy val i_l_lParser : PackratParser[RuleStruct] =
		"I_L_L" ^^ { _ => I_L_L() }

	lazy val i_r_rParser : PackratParser[RuleStruct] =
		"I_R_R" ^^ { _ => I_R_R() }

	lazy val i_l_r2Parser : PackratParser[RuleStruct] =
		"I_L_R2" ^^ { _ => I_L_R2() }

	lazy val a_lParser : PackratParser[RuleStruct] =
		"A_L" ^^ { _ => A_L() }

	lazy val p_rParser : PackratParser[RuleStruct] =
		"P_R" ^^ { _ => P_R() }

	lazy val i_r_l2Parser : PackratParser[RuleStruct] =
		"I_R_L2" ^^ { _ => I_R_L2() }

	lazy val a_l2Parser : PackratParser[RuleStruct] =
		"A_L2" ^^ { _ => A_L2() }

	lazy val w_rParser : PackratParser[RuleStruct] =
		"W_R" ^^ { _ => W_R() }

	def parseRuleStruct(s:String) : Option[RuleStruct] = parseAll(rulestructParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulezerParser : PackratParser[RuleZer] = 
		premParser | partialParser | idParser | "(" ~> rulezerParser <~ ")"

	lazy val premParser : PackratParser[RuleZer] =
		"Prem" ^^ { _ => Prem() }

	lazy val partialParser : PackratParser[RuleZer] =
		"Partial" ^^ { _ => Partial() }

	lazy val idParser : PackratParser[RuleZer] =
		"Id" ^^ { _ => Id() }

	def parseRuleZer(s:String) : Option[RuleZer] = parseAll(rulezerParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruleParser : PackratParser[Rule] =
		rulecutParser ^^ { case a => RuleCuta(a) } |
		rulelParser ^^ { case a => RuleLa(a) } |
		rulestructParser ^^ { case a => RuleStructa(a) } |
		rulezerParser ^^ { case a => RuleZera(a) } |
		"Macro" ~> stringParser ~ prooftreeParser ^^ { case a ~ pt => RuleMacro(a, pt) } |
		"Fail" ^^ { _ => Fail() }

	def parseRule(s:String) : Option[Rule] = parseAll(ruleParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}
/*parser_calc_structure_rules-END*/


/*/*uncommentL?core_compiled-BEGIN*/*//*uncommentL?core_compiled-END*/
	def prooftreeListParser : Parser[List[Prooftree]] =
		"[" ~ "]" ^^ { _ => List[Prooftree]() } |
		"[" ~> rep(prooftreeParser <~ ",") ~ prooftreeParser <~ "]" ^^ { case list ~ last => list ++ List[Prooftree](last) }

	def prooftreeParser : Parser[Prooftree] =
		sequentParser ~ "<==" ~ "(" ~ ruleParser ~ ")" ~ prooftreeListParser ^^ { case a ~ "<==" ~ "(" ~ b ~ ")" ~ c => Prooftreea(a, b, c) } |
		"(" ~> sequentParser ~ "<==" ~ "(" ~ ruleParser ~ ")" ~ prooftreeListParser  <~ ")" ^^ { case a ~ "<==" ~ "(" ~ b ~ ")" ~ c => Prooftreea(a, b, c) }

	def parseProoftree(s:String) : Option[Prooftree] = parseAll(prooftreeParser,s) match {
		case Success(result, _) => Some(result)
		case NoSuccess(msg, _) => println(msg);None
	}
/*uncommentR?core_compiled-BEGIN*//*/*uncommentR?core_compiled-END*/*/

	def main(args:Array[String]) {
/*/*uncommentL?Sequent-BEGIN*/*//*uncommentL?Sequent-END*/
		if (args.length == 1){
			Some(JSON.parseFull(args(0))) match {
      			case Some(L(list)) =>
      				val buf = new scala.collection.mutable.ListBuffer[String]()
					for (e <- list) parseSequent(e) match {
				    	case Some(r) => 
				    		buf += PrintCalc.sequentToString(r, PrintCalc.ISABELLE)
				    	case None => buf += ""
				    }
				    print( JSONArray(buf.toList) )
				case _ => print("[]")
		    }
		}
		else if (args.length == 2){
			Some(JSON.parseFull(args(1))) match {
      			case Some(L(list)) =>
      				val buf = new scala.collection.mutable.ListBuffer[String]()
					for (e <- list) parseSequent(e) match {
				    	case Some(r) => 
				    		if(args(0) == "se") buf += PrintCalc.sequentToString(r, PrintCalc.ISABELLE_SE)
				    		else buf += PrintCalc.sequentToString(r, PrintCalc.ISABELLE)
				    	case None => buf += ""
				    }
				    print( JSONArray(buf.toList) )
				case _ => print("[]")
		    }
		}  
		else print("[]")
/*uncommentR?Sequent-BEGIN*//*/*uncommentR?Sequent-END*/*/
	}
}

class CC[T] {
  def unapply(a:Option[Any]):Option[T] = if (a.isEmpty) {
    None
  } else {
    Some(a.get.asInstanceOf[T])
  }
}

object L extends CC[List[String]]


/* the following code snippet was adapted from code found at https://gist.github.com/hisui/1692021 */

trait OperatorPrecedenceParsers extends PackratParsers {

  trait Op[+T,U] {
    def lhs:Double = 0
    def rhs:Double = 0
    def parse:PackratParser[T]
  }

  case class Infix[T,U]
  ( override val lhs:Double
  , override val rhs:Double)
  ( override val parse:PackratParser[T])(val map:(T,U,U) => U) extends Op[T,U]

  case class Prefix[T,U](override val rhs:Double)(override val parse:PackratParser[T])(val map:(T,U) => U) extends Op[T,U]
  case class Suffix[T,U](override val lhs:Double)(override val parse:PackratParser[T])(val map:(T,U) => U) extends Op[T,U]

  def operators[T,U](opseq:Op[T,U]*)(innermost:PackratParser[U]) = new PackratParser[U] {

    type Ops = List[(Op[T,U],T)]
    type Out = List[U]

    val (prefixOps, suffixOps) = opseq.partition( _.isInstanceOf[Prefix[_,_]] )

    def findPrefix(ops:Ops, out:Out, in:Input):ParseResult[U] = {

      prefixOps.iterator.map(e => e -> e.parse(in))
        .collectFirst {
          case (op, Success(o, in2)) => findPrefix(op -> o :: ops, out, in2)
        }
        .getOrElse{ //println(innermost(in)); 
        	innermost(in)
          .flatMapWithNext(o => in => findSuffix(ops, o :: out, in)) }
    }
    
    def fold(lhs:Double, ops:Ops, out:Out):(Ops,Out) =
      ops match {
        case (op, o)::ops if op.rhs < lhs =>
          fold(lhs, ops, (( (op, out): @unchecked ) match {
            case (op:Prefix[T,U], x::xs) => op.map(o, x) :: xs
            case (op:Suffix[T,U], x::xs) => op.map(o, x) :: xs
            case (op: Infix[T,U], y::x::xs) => op.map(o, x, y) :: xs
          }))
        case _ => ops -> out
      }

    def findSuffix(ops:Ops, out:Out, in:Input):ParseResult[U] =
      suffixOps.iterator.map(e => e -> e.parse(in))
        .collectFirst {
          case (op, Success(o, in)) =>
            val $ = fold(op.lhs, ops, out)
            (if (op.isInstanceOf[Infix[_,_]])
              findPrefix _ else
              findSuffix _ ) ((op, o) :: $._1, $._2, in)
        }
        .getOrElse(Success(fold(1/0.0, ops, out)._2.head, in))

    override def apply(in:Input):ParseResult[U] = findPrefix(Nil, Nil, in)

  }
}