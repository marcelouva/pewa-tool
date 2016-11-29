/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= programa_wap
 * loopUnroll= 1
 * removeQuantifiers= true
 * strictUnrolling= true
 */ 

//-------------- prelude--------------//
module moduleId
open Integer32
open util/sequniv as sequniv
fun fun_reach[h: univ, 
              type: set univ, 
              field: univ -> univ
]: set univ { 
  h.*(field & type->(type+null)) & type 
}
abstract sig char {}
abstract sig Exception{}
one sig E1 extends Exception{}
fun shl[l,r: Int]: Int { l << r } 
fun sshr[l,r: Int]: Int { l >> r } 
fun ushr[l,r: Int]: Int { l >>> r } 

fun fun_univ_equals[
  l:univ, 
  r: univ 
]: boolean { 
  (equ[l,r]) => true else false 
} 

fun fun_set_add[
  l: set univ,
  e: univ
]: set univ { 
  l+e 
} 

fun fun_set_remove[
  l: set univ,
  e: univ
]: set univ {
  l-e
}
fun fun_set_contains[
  l: set univ,
  e: univ
]: boolean {
  (e in l) => true else false 
} 
pred isSubset[
  l: set univ,
  r: set univ
] {
  (l in r) 
} 
pred isNotSubset[
  l: set univ,
  r: set univ
] {
  (l !in r) 
} 
fun fun_set_size[s: set univ]: Int { #s } 

fun fun_not_empty_set[s: set univ]: boolean { (#s = 0) => false else true } 

pred pred_empty_set[l: set univ] { (no l) } 

pred pred_set_some[l: set univ] { some l } 

pred pred_set_one[l: set univ] { one l } 

pred pred_set_lone[l: set univ] { lone l } 


fun fun_set_intersection[
  l: set univ,
  r: set univ
]: set univ {
  l & r 
} 
fun fun_set_difference[
  l: set univ,
  r: set univ
]: set univ {
  l - r 
} 
fun fun_set_sum[
  s: set Int
]: Int {
  sum s 
} 
pred pred_empty_list[l: seq univ] { (no l) } 

fun fun_list_add[
  l: seq univ,
  e: univ
]: seq univ {
  sequniv/add[l,e] 
} 

fun fun_list_get[
  l: seq univ, 
  index: Int
]: univ { 
  index.l 
} 

fun fun_list_contains[
  l: seq univ, 
  e: univ
]: boolean { 
  (e in Int.l) => true else false 
} 

fun fun_list_remove[
  l: seq univ, 
  index: Int
]: seq univ { 
  sequniv/delete[l,index] 
} 

fun fun_list_size[s: seq univ]: Int { #s } 

fun fun_list_equals[
  s1:seq univ, 
  s2: seq univ
]: boolean { 
  (s1=s2) => true else false 
} 

fun fun_list_empty[s: seq univ]: boolean { (#s = 0) => true else false } 

pred pred_empty_map[map: univ -> univ] { (no map) } 

fun fun_map_put[
  map: univ->univ, 
  k: univ, 
  v: univ
]: univ-> univ { 
  map ++ (k->v) 
}

fun fun_map_contains_key[
  map: univ -> univ, 
  k: univ
]: boolean { 
  (some k.map) => true else false 
}

fun fun_map_remove[
  map: univ -> univ, 
  k: univ
]: univ->univ {
  map - (k->univ) 
} 

fun fun_map_get[
  map: univ -> univ, 
  k: univ
]: univ { 
  (some k.map) => k.map else null 
} 

fun fun_map_is_empty[
  map: univ -> univ, 
]: boolean { 
  (some map) => false else true 
}

fun fun_map_clear[
  mapEntries1: univ -> univ -> univ, 
  map: univ
]: univ -> univ -> univ { 
  mapEntries1 - (map -> univ -> univ)
}

fun fun_map_size[
  map: univ -> univ, 
]: univ {
  #map 
} 

pred isEmptyOrNull[u: univ] { u in null } 
fun fun_closure[
  rel: univ -> univ 
]: univ -> univ {
  ^rel 
} 

fun fun_reflexive_closure[
  rel: univ -> univ 
]: univ -> univ {
  *rel 
} 

fun fun_transpose[
  rel: univ -> univ 
]: univ -> univ {
  ~rel 
} 


fun rel_override[
  r:univ->univ,
  k:univ, 
  v:univ
]: univ->univ { 
  r - (k->univ) + (k->v) 
} 


pred pred_in[n: univ, t: set univ] { n in t } 

pred instanceOf[n: univ, t: set univ] { n in t } 

pred isCasteableTo[n: univ, t: set univ] { (n in t) or (n = null) }
abstract sig actionExec{}
pred pos_gen_Int[y:Int]{
 some i: Int | y = i
}
pred pos_gen_I32[y:JavaPrimitiveIntegerValue]{
  some i: JavaPrimitiveIntegerValue | pred_java_primitive_integer_value_eq[y,i]
}
pred pos_add_null[s:JavaPrimitiveIntegerValue,b:boolean]{
   equ[s,null] implies equ[b,false]
   not equ[s,null] implies equ[b,true]
}


pred pos_verify_null[s:JavaPrimitiveIntegerValue+null,b:boolean]{
   equ[s,null] implies equ[b,false]
   not equ[s,null] implies equ[b,true]
}
pred pos_vaciar[s:set univ]{
    no s
}
pred sequence[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue] {
    all x: s.JavaPrimitiveIntegerValue | int32_prevs[x] in s.JavaPrimitiveIntegerValue 
}






pred precondition_Lista_addf[]{}

pred postcondition_Lista_addf[
  intJ_1: JavaPrimitiveIntegerValue,
  thisType_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  thisType_1':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{
  sequence[thisType_1] and sequence[thisType_1'] and
  thisType_1'[i320]=intJ_1  and
  (all a,b:JavaPrimitiveIntegerValue |  
	(a->b) in thisType_1 implies  (fun_java_primitive_integer_value_add[a,i321]->b) in thisType_1') and
        JavaPrimitiveIntegerValue.thisType_1'= JavaPrimitiveIntegerValue.thisType_1 + intJ_1
}
/*scope:1*/


pred precondition_Lista_push[]{}

pred postcondition_Lista_push[
  intJ_1: JavaPrimitiveIntegerValue,
  thisType_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  thisType_1':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{
  sequence[thisType_1] and sequence[thisType_1'] and
  thisType_1'[i320]=intJ_1  and
  (all a,b:JavaPrimitiveIntegerValue |  
	(a->b) in thisType_1 implies  (fun_java_primitive_integer_value_add[a,i321]->b) in thisType_1') and
        JavaPrimitiveIntegerValue.thisType_1'= JavaPrimitiveIntegerValue.thisType_1 + intJ_1
}
/*scope:1*/




one
sig Lista_pop extends actionExec{}
one sig TS_clear_0 extends actionExec{}
one sig Lista_poll_first extends actionExec{}
one sig contains extends actionExec{}
one sig Lista_element_m extends actionExec{}
one sig Lista_offer extends actionExec{}
one sig Lista_peekLast extends actionExec{}
one sig add extends actionExec{}
one sig Lista_offer_last extends actionExec{}
one sig peek extends actionExec{}
one sig Lista_poll_last extends actionExec{}
one sig Lista_remove_last extends actionExec{}
one sig Lista_offerFirst extends actionExec{}
one sig Lista_set_element extends actionExec{}
one sig Lista_indexOf extends actionExec{}
one sig Listaremove_first extends actionExec{}
one sig Lista_getLast extends actionExec{}
one sig Lista_remove2 extends actionExec{}
one sig Listaremove extends actionExec{}
one sig Lista_poll extends actionExec{}
one sig get_first extends actionExec{}
one sig Lista_add_last extends actionExec{}
one sig Lista_get extends actionExec{}
one sig Lista_add_first extends actionExec{}
one sig Lista_push extends actionExec{}
one sig Lista_isEmpty extends actionExec{}
one sig TS_size extends actionExec{}
one sig Lista_remove_m extends actionExec{}
one sig Lista_last_indexOf extends actionExec{}
one sig Lista_remove_fo extends actionExec{}
one sig peek_first extends actionExec{}
one sig Lista_add2 extends actionExec{}
pred pred_not[p_0:JavaPrimitiveIntegerValue,p_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
p_2:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{ not(postcondition_Lista_addf[p_0,p_1,p_2])}




pred gen_intJ[
  x_1: JavaPrimitiveIntegerValue
]{
  TruePred[]
  and 
  pos_gen_I32[x_1]
}




pred Lista_push[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_push[]
  and 
  postcondition_Lista_push[intJ_1_0,
                          thisType_1_0,
                          thisType_1_1]
}


pred init_set[
  s_1: set univ
]{
  TruePred[]
  and 
  pos_vaciar[s_1]
}



pred gen_intA[
  x_1: Int
]{
  TruePred[]
  and 
  pos_gen_Int[x_1]
}




one sig QF {
  ac_1: actionExec,
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  valid_bool_1: boolean,
  valid_intA_1: boolean,
  valid_intJ_1: boolean
}


fact {
  precondition_Lista_addf[]
}

fact {
  QF.valid_intA_1=false
}

fact {
  QF.valid_bool_1=false
}

fact {
  QF.valid_intJ_1=false
}

fact {
  gen_intJ[QF.intJ_1_1]
}

fact {
  Lista_push[QF.intJ_1_1,
            QF.thisType_1_0,
            QF.thisType_1_1]

}

fact {
  QF.ac_1=Lista_push
}

pred programa_wap{
  pred_not[QF.intJ_1_1,
          QF.thisType_1_0,
          QF.thisType_1_1]
}




  one sig i32m1  extends JavaPrimitiveIntegerValue{}  one sig i320  extends JavaPrimitiveIntegerValue{} 
 one sig i321  extends JavaPrimitiveIntegerValue{}  one sig i322  extends JavaPrimitiveIntegerValue{}  one sig i323  extends JavaPrimitiveIntegerValue{}  one sig i32100  extends JavaPrimitiveIntegerValue{}  one sig i32200  extends JavaPrimitiveIntegerValue{}  

fact{ b00 in i32m1->true  + i320->false  + i321->true  + i322->false  + i323->true  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->true  + i322->false  + i323->true  + i32100->false  + i32200->false  in  b00 and  b01 in i32m1->true  + i320->false  + i321->false  + i322->true  + i323->true  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->true  + i323->true  + i32100->false  + i32200->false  in  b01 and  b02 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->false  in  b02 and  b03 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->true  in  b03 and  b04 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in  b04 and  b05 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->false  in  b05 and  b06 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->true  in  b06 and  b07 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->true  in  b07 and  b08 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in  b08 and  b09 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in  b09 and b10 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b10 and b11 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b11 and b12 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b12 and b13 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b13 and b14 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b14 and b15 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b15 and b16 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b16 and b17 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b17 and b18 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b18 and b19 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b19 and b20 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b20 and b21 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b21 and b22 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b22 and b23 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b23 and b24 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b24 and b25 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b25 and b26 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b26 and b27 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b27 and b28 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b28 and b29 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b29 and b30 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b30 and b31 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b31} fact { QF.intJ_1_0=i320}   run  programa_wap for 0 but 9 JavaPrimitiveIntegerValue  fun int32_max[es: set (i320+i321+i322)] : lone (i320+i321+i322) { es - es.(   i321->(i320)   +   i322->(i320+i321) )}fun int32_prevs[e: i320+i321+i322] :set (i320+i321+i322) { e.(   i321->(i320)   +   i322->(i320+i321) )}pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {	let dom = s.JavaPrimitiveIntegerValue |		(no dom and res = i320) or 		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])}/*FIN_PRE*/
fact{ QF.ac_1=Lista_push}

