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




pred precondition_Lista_pop
[values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{    
  not (no values)
}


pred postcondition_Lista_pop 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{

   sequence[values] 
  (some size:JavaPrimitiveIntegerValue | myseq_card[values',size] and  values'=values-(size->JavaPrimitiveIntegerValue))
}
/*scope:1*/





pred postcondition_TS_clear
[values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,values': JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]
{ no values'}

pred precondition_TS_clear
[v: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{}
/*scope:0*/
pred precondition_Lista_poll_first
[values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{    
  not (no values)
}

pred postcondition_Lista_poll_first 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue+null
]
{



  (ret=null and (no values) and (no values'))
  

or
(sequence[values] and sequence[values'] and
(some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and 
         values.JavaPrimitiveIntegerValue=(values'.JavaPrimitiveIntegerValue)+fun_java_primitive_integer_value_sub[size,i321]) and 
    pred_java_primitive_integer_value_eq[ret,i320.values]  and
   (all a,b:JavaPrimitiveIntegerValue | (a->b) in values and  pred_java_primitive_integer_value_neq[a,i320]  
	implies (fun_java_primitive_integer_value_sub[a,i321]->b) in values') )
}
/*scope:1*/


pred postcondition_Lista_contains[elem: JavaPrimitiveIntegerValue,values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,return_bool: boolean]
{ 

 sequence[values] and 
values'=values and

( not (no values.elem ) implies equ[return_bool, true])
     and
  ((no values.elem ) implies equ[return_bool, false] )

}

pred precondition_Lista_contains[]{
}
/*scope:0*/

pred postcondition_Lista_element_m 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{
    sequence[values] and values'=values and

    pred_java_primitive_integer_value_eq[ret,i320.values]
} 


pred precondition_Lista_element_m
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{      
    sequence[values] and not (no values)
}
/*scope:0*/ 
pred postcondition_Lista_offer[
  intJ_1: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: boolean
]
{
   sequence[values] and sequence[values'] and
  (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  values'=values+(size->intJ_1))
   equ[ret,true]
}


pred precondition_Lista_offer
[]{}
/*scope:1*/


pred postcondition_Lista_peekLast 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue]
{
   sequence[values'] and 
    sequence[values] and values'=values and

   (some size:JavaPrimitiveIntegerValue | 
		myseq_card[values,size] and 
ret=values[fun_java_primitive_integer_value_sub[size,i321]]

)
}


pred precondition_Lista_peekLast
[  thisType_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]
{      
    sequence[thisType_1] and not (no thisType_1)
}
/*scope:0*/


pred precondition_Lista_add[]{}

pred postcondition_Lista_add[
  intJ_1: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{
  sequence[values] and
  (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  values'=values+(size->intJ_1))
}
/*scope:1*/








pred postcondition_Lista_offer_last[
  intJ_1: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: boolean
]
{
   sequence[values]  and
  (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  values'=values+(size->intJ_1)) and
   equ[ret,true]
}


pred precondition_Lista_offer_last
[]{}
/*scope:1*/


pred postcondition_Lista_peek 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{

    sequence[values]  and values'=values and
 pred_java_primitive_integer_value_eq[ret,i320.values]
} 


pred precondition_Lista_peek
[
  thisType_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{      
    sequence[thisType_1] and not (no thisType_1)
}
/*scope:0*/ 
pred precondition_Lista_poll_last
[values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{    
  not (no values)
}


pred postcondition_Lista_pollLast 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue+null
]
{

  (ret=null and (no values) and (no values'))
  or

  ( sequence[values] and  sequence[values'] and
  (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  values'=values-((fun_java_primitive_integer_value_sub[size,i321])->JavaPrimitiveIntegerValue) and 
  ret=values[fun_java_primitive_integer_value_sub[size,i321]])
)
}
/*scope:1*/

pred precondition_Lista_remove_last
[values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{    
  not (no values)
}


pred postcondition_Lista_remove_last 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{
   sequence[values] and 
  (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  values'=values-((fun_java_primitive_integer_value_sub[size,i321])->JavaPrimitiveIntegerValue)
and

ret=values[fun_java_primitive_integer_value_sub[size,i321]])

}
/*scope:1*/












pred precondition_Lista_offer_first[]{}

pred postcondition_offer_first[
  intJ_1: JavaPrimitiveIntegerValue,
  thisType_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  thisType_1':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: boolean  
]
{
  sequence[thisType_1] and sequence[thisType_1'] and
  
  (i320->intJ_1) in thisType_1'  and   ret=true and 
  (all a,b:JavaPrimitiveIntegerValue|  
	(a->b) in thisType_1 implies  (fun_java_primitive_integer_value_add[a,i321]->b) in thisType_1')
  and
   JavaPrimitiveIntegerValue.thisType_1'= JavaPrimitiveIntegerValue.thisType_1 + intJ_1


}
/*scope:1*/



pred precondition_Lista_set_element
[ indice:JavaPrimitiveIntegerValue,values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]
{  not (no indice.values) and sequence[values]}


pred postcondition_Lista_set_element
[
  indice: JavaPrimitiveIntegerValue,
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  retorno:JavaPrimitiveIntegerValue
]
{

sequence[values]  and
retorno=indice.values and values'=values++(indice->elem)

}
/*scope:0*/


pred postcondition_Lista_indexOf
[
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret:JavaPrimitiveIntegerValue
] {
    sequence[values] and values'=values and
    ( ((no values.elem)  and pred_java_primitive_integer_value_eq[i32m1,ret]) 

or 
    (not(no values.elem) and (some min:values.elem | 
                                    (all e:values.elem | pred_java_primitive_integer_value_lte[min,e]) and 
				      pred_java_primitive_integer_value_eq[min,ret])) 

)
}

pred precondition_Lista_indexOf[]{}
/*scope:0*/






pred precondition_Listaremove_first
[values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{    
  not (no values)
}

pred postcondition_Listaremove_first 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{
 sequence[values]and sequence[values'] and
//(some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  values'=values+((fun_java_primitive_integer_value_sub[size,i321])->JavaPrimitiveIntegerValue) ) and
    pred_java_primitive_integer_value_eq[ret,i320.values]  
and    (all a,b:JavaPrimitiveIntegerValue | ((a->b) in values and  pred_java_primitive_integer_value_neq[a,i320])  implies (fun_java_primitive_integer_value_sub[a,i321]->b) in values') 

and (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  not (((fun_java_primitive_integer_value_sub[size,i321])->JavaPrimitiveIntegerValue) in values') ) 

  






}
/*scope:1*/
pred postcondition_Lista_getLast 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue]
{
   sequence[values'] and 
    sequence[values] and values'=values and

   (some size:JavaPrimitiveIntegerValue | 
		myseq_card[values,size] and 
ret=values[fun_java_primitive_integer_value_sub[size,i321]]

)
}


pred precondition_Lista_getLast
[  thisType_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]
{      
    sequence[thisType_1] and not (no thisType_1)
}
/*scope:0*/


pred postcondition_Lista_remove2
[
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: boolean
]
{
   (no values.elem  implies (ret=false and values=values')) 
    or 
   ( 


sequence[values] and sequence[values'] and 
(JavaPrimitiveIntegerValue.values-elem=JavaPrimitiveIntegerValue.values') and  

(some i :JavaPrimitiveIntegerValue |
	    (i->elem) in values and (all a,b:JavaPrimitiveIntegerValue | (a->b) in values  implies (
					( pred_java_primitive_integer_value_lt[a,i]  implies (a->b) in values')    and
					( pred_java_primitive_integer_value_lt[i,a]  implies ((fun_java_primitive_integer_value_sub[a,i321])->b) in values')
                                    ) 
                                    ) and  




ret=true)and




 (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  not (((fun_java_primitive_integer_value_sub[size,i321])->JavaPrimitiveIntegerValue) in values') ) 


)
}




pred precondition_Lista_remove2
[  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{ }
/*scope:1*/


pred precondition_Listaremove
[values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{    
  not (no values)
}

pred postcondition_Listaremove 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{
 sequence[values]and sequence[values'] and
//(some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  values'=values+((fun_java_primitive_integer_value_sub[size,i321])->JavaPrimitiveIntegerValue) ) and
    pred_java_primitive_integer_value_eq[ret,i320.values]  
and    (all a,b:JavaPrimitiveIntegerValue | ((a->b) in values and  pred_java_primitive_integer_value_neq[a,i320])  implies (fun_java_primitive_integer_value_sub[a,i321]->b) in values') 

and (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  not (((fun_java_primitive_integer_value_sub[size,i321])->JavaPrimitiveIntegerValue) in values') ) 

  






}
/*scope:1*/
pred precondition_Lista_poll
[values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{    
  not (no values)
}

pred postcondition_Lista_poll 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue+null
]
{
(
  (ret=null and (no values') and (no values))
)
or
(
sequence[values] and sequence[values'] and
(some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and 
         values.JavaPrimitiveIntegerValue=(values'.JavaPrimitiveIntegerValue)+fun_java_primitive_integer_value_sub[size,i321]) and 
    pred_java_primitive_integer_value_eq[ret,i320.values]  and
   (all a,b:JavaPrimitiveIntegerValue | (a->b) in values and  pred_java_primitive_integer_value_neq[a,i320]  
	implies (fun_java_primitive_integer_value_sub[a,i321]->b) in values') 
)

}
/*scope:1*/









pred postcondition_Lista_get_first 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{
   sequence[values] and values'=values and
    pred_java_primitive_integer_value_eq[ret,values[i320]]
} 


pred precondition_Lista_get_first
[
  thisType_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{      
    sequence[thisType_1] and not (no thisType_1)
}
/*scope:0*/ 
pred precondition_Lista_addl[]{}

pred postcondition_Lista_addl[
  intJ_1: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{
   sequence[values] and 
  (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  values'=values+(size->intJ_1))
}
/*scope:1*/




pred postcondition_Lista_get 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  indice: JavaPrimitiveIntegerValue,
  retorno: JavaPrimitiveIntegerValue
]
{
      sequence[values] and values'=values and  pred_java_primitive_integer_value_eq[retorno,values[indice]]
    

}


pred precondition_Lista_get
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  indice: JavaPrimitiveIntegerValue
]
{
   not (no indice.values) and sequence[values] 

}
/*scope:0*/


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
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{
  sequence[values] and sequence[values'] and
  values'[i320]=intJ_1  and
  (all a,b:JavaPrimitiveIntegerValue |  
	(a->b) in values implies  (fun_java_primitive_integer_value_add[a,i321]->b) in values')
 and
        JavaPrimitiveIntegerValue.values'= JavaPrimitiveIntegerValue.values + intJ_1
}
/*scope:1*/


pred postcondition_Lista_isEmpty 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  return_bool: boolean 
]
{
      (sequence[values] and values'=values)and  (equ[return_bool, true] iff no values)
}


pred precondition_Lista_isEmpty
[]{}
/*scope:0*/


pred precondition_TS_size[]{}

pred postcondition_TS_size [return_int':JavaPrimitiveIntegerValue, 
    values: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
    values': JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]
{ 

  sequence[values] and values'=values and  myseq_card[values,return_int']
}
/*scope:0*/










pred precondition_Lista_remove_m
[
  indice:JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]{  not (no indice.values)
}

pred postcondition_Lista_remove_m
[
  indice:JavaPrimitiveIntegerValue, 
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{

  sequence[values] and sequence[values']  and

  pred_java_primitive_integer_value_eq[ret,indice.values]  

and 

 (all a,b:JavaPrimitiveIntegerValue | (a->b) in values implies 
	(( pred_java_primitive_integer_value_lt[a,indice] implies (a->b) in  values') and
	 ( pred_java_primitive_integer_value_gt[a,indice] implies (fun_java_primitive_integer_value_sub[a,i321]->b) in values'))
) and 
  JavaPrimitiveIntegerValue.values' + indice.values = JavaPrimitiveIntegerValue.values  

and (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  not (((fun_java_primitive_integer_value_sub[size,i321])->JavaPrimitiveIntegerValue) in values') ) 

}
/*scope:1*/



pred postcondition_Lista_lio
[
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret:JavaPrimitiveIntegerValue
]
{
     sequence[values]  and values'=values and(
    ( (no values.elem)  and pred_java_primitive_integer_value_eq[i32m1,ret]) or 
    (not(no values.elem) and (some max:values.elem | 
                                    (all e:values.elem | pred_java_primitive_integer_value_lte[e,max]) and 
				      pred_java_primitive_integer_value_eq[max,ret])) 

)
}

pred precondition_Lista_lio[]{}
/*scope:0*/

pred postcondition_Lista_remove_fo
[
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: boolean
]
{
   ((no values.elem)  and ret=false and values=values') 
    or 
   (some i :JavaPrimitiveIntegerValue |
	    (i->elem) in values and (all a,b:JavaPrimitiveIntegerValue | (a->b) in values  implies (
					( pred_java_primitive_integer_value_lt[a,i]  implies (a->b) in values')    and
					( pred_java_primitive_integer_value_lt[i,a]  implies ((fun_java_primitive_integer_value_sub[a,i321])->b) in values')
                                    ) 
                                    )  and

ret=true and
JavaPrimitiveIntegerValue.values-elem=JavaPrimitiveIntegerValue.values'  
 and (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  not (((fun_java_primitive_integer_value_sub[size,i321])->JavaPrimitiveIntegerValue) in values') ) 

)
}




pred precondition_Lista_remove_fo
[]{ }
/*scope:1*/




pred postcondition_Lista_peek_first 
[
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{

    sequence[values]  and values'=values and
 pred_java_primitive_integer_value_eq[ret,i320.values]
} 


pred precondition_Lista_peek_first
[
  thisType_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{      
    sequence[thisType_1] and not (no thisType_1)
}
/*scope:0*/ 

pred precondition_Lista_add2
[
  indice: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]

{
   not (no indice.values) and  sequence[values]  
}




pred postcondition_Lista_add2
[
  elem: JavaPrimitiveIntegerValue,
  indice:JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{
  sequence[values] and sequence[values'] and
       (indice->elem) in values' and
        (all a,b:JavaPrimitiveIntegerValue | (a->b) in values implies (
	(pred_java_primitive_integer_value_lt[a,indice] implies  (a->b) in values' )
					and
	(pred_java_primitive_integer_value_gt[a,indice] implies  (fun_java_primitive_integer_value_add[a,i321]->b) in values' )
)) and 
   JavaPrimitiveIntegerValue.values'= JavaPrimitiveIntegerValue.values + elem
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
pred pred_not[p_0:JavaPrimitiveIntegerValue,p_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,p_2:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{ not(postcondition_Lista_addf[p_0,p_1,p_2])}
 



pred Lista_offer_last[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_bool_1: boolean
]{
  precondition_Lista_offer_last[]
  and 
  postcondition_Lista_offer_last[intJ_1_0,
                                thisType_1_0,
                                thisType_1_1,
                                return_bool_1]
}


pred Lista_set_element[
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_2_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_set_element[intJ_1_0,
                                thisType_1_0]
  and 
  postcondition_Lista_set_element[intJ_1_0,
                                 intJ_2_0,
                                 thisType_1_0,
                                 thisType_1_1,
                                 return_intJ_1_1]
}


pred contains[
  return_bool_1: boolean,
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_contains[]
  and 
  postcondition_Lista_contains[intJ_1_0,
                              thisType_1_0,
                              thisType_1_1,
                              return_bool_1]
}


pred Lista_element_m[
  return_intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_element_m[thisType_1_0]
  and 
  postcondition_Lista_element_m[thisType_1_0,
                               thisType_1_1,
                               return_intJ_1_1]
}


pred Lista_remove_m[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_remove_m[intJ_1_0,
                             thisType_1_0]
  and 
  postcondition_Lista_remove_m[intJ_1_0,
                              thisType_1_0,
                              thisType_1_1,
                              return_intJ_1_1]
}


pred Lista_getLast[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_getLast[thisType_1_0]
  and 
  postcondition_Lista_getLast[thisType_1_0,
                             thisType_1_0,
                             return_intJ_1_1]
}


pred gen_intJ[
  x_1: JavaPrimitiveIntegerValue
]{
  TruePred[]
  and 
  pos_gen_I32[x_1]
}


pred Lista_offer[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_bool_1: boolean
]{
  precondition_Lista_offer[]
  and 
  postcondition_Lista_offer[intJ_1_0,
                           thisType_1_0,
                           thisType_1_1,
                           return_bool_1]
}


pred Lista_isEmpty[
  return_bool_1: boolean,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_isEmpty[]
  and 
  postcondition_Lista_isEmpty[thisType_1_0,
                             thisType_1_1,
                             return_bool_1]
}


pred Lista_get[
  return_intJ_1_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_get[thisType_1_0,
                        intJ_1_0]
  and 
  postcondition_Lista_get[thisType_1_0,
                         thisType_1_1,
                         intJ_1_0,
                         return_intJ_1_1]
}


pred get_first[
  return_intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_get_first[thisType_1_0]
  and 
  postcondition_Lista_get_first[thisType_1_0,
                               thisType_1_1,
                               return_intJ_1_1]
}


pred peek[
  return_intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_peek[thisType_1_0]
  and 
  postcondition_Lista_peek[thisType_1_0,
                          thisType_1_1,
                          return_intJ_1_1]
}


pred Lista_add2[
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_2_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_add2[intJ_2_0,
                         thisType_1_0]
  and 
  postcondition_Lista_add2[intJ_1_0,
                          intJ_2_0,
                          thisType_1_0,
                          thisType_1_1]
}


pred Listaremove[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Listaremove[thisType_1_0]
  and 
  postcondition_Listaremove[thisType_1_0,
                           thisType_1_1,
                           return_intJ_1_1]
}


pred Lista_add_last[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_addl[]
  and 
  postcondition_Lista_addl[intJ_1_0,
                          thisType_1_0,
                          thisType_1_1]
}


pred Lista_pop[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_pop[thisType_1_0]
  and 
  postcondition_Lista_pop[thisType_1_0,
                         thisType_1_1,
                         return_intJ_1_1]
}


pred Lista_remove2[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_bool_1: boolean
]{
  precondition_Lista_remove2[thisType_1_0]
  and 
  postcondition_Lista_remove2[intJ_1_0,
                             thisType_1_0,
                             thisType_1_1,
                             return_bool_1]
}


pred Lista_peekLast[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_peekLast[thisType_1_0]
  and 
  postcondition_Lista_peekLast[thisType_1_0,
                              thisType_1_0,
                              return_intJ_1_1]
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


pred Listaremove_first[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Listaremove_first[thisType_1_0]
  and 
  postcondition_Listaremove_first[thisType_1_0,
                                 thisType_1_1,
                                 return_intJ_1_1]
}


pred init_set[
  s_1: set univ
]{
  TruePred[]
  and 
  pos_vaciar[s_1]
}


pred Lista_poll[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue + null
]{
  precondition_Lista_poll[thisType_1_0]
  and 
  postcondition_Lista_poll[thisType_1_0,
                          thisType_1_1,
                          return_intJ_1_1]
}


pred add[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_add[]
  and 
  postcondition_Lista_add[intJ_1_0,
                         thisType_1_0,
                         thisType_1_1]
}


pred TS_size[
  return_intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_TS_size[]
  and 
  postcondition_TS_size[return_intJ_1_1,
                       thisType_1_0,
                       thisType_1_1]
}


pred Lista_remove_last[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_remove_last[thisType_1_0]
  and 
  postcondition_Lista_remove_last[thisType_1_0,
                                 thisType_1_1,
                                 return_intJ_1_1]
}


pred Lista_offerFirst[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_bool_1: boolean
]{
  precondition_Lista_offer_first[]
  and 
  postcondition_offer_first[intJ_1_0,
                           thisType_1_0,
                           thisType_1_1,
                           return_bool_1]
}


pred peek_first[
  return_intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_peek_first[thisType_1_0]
  and 
  postcondition_Lista_peek_first[thisType_1_0,
                                thisType_1_1,
                                return_intJ_1_1]
}


pred Lista_add_first[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_addf[]
  and 
  postcondition_Lista_addf[intJ_1_0,
                          thisType_1_0,
                          thisType_1_1]
}


pred gen_intA[
  x_1: Int
]{
  TruePred[]
  and 
  pos_gen_Int[x_1]
}


pred TS_clear_0[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_TS_clear[thisType_1_0]
  and 
  postcondition_TS_clear[thisType_1_0,
                        thisType_1_1]
}


pred Lista_poll_last[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue + null
]{
  precondition_Lista_poll_last[thisType_1_0]
  and 
  postcondition_Lista_pollLast[thisType_1_0,
                              thisType_1_1,
                              return_intJ_1_1]
}


pred Lista_last_indexOf[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_lio[]
  and 
  postcondition_Lista_lio[intJ_1_0,
                         thisType_1_0,
                         thisType_1_1,
                         return_intJ_1_1]
}


pred Lista_remove_fo[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_bool_1: boolean
]{
  precondition_Lista_remove_fo[]
  and 
  postcondition_Lista_remove_fo[intJ_1_0,
                               thisType_1_0,
                               thisType_1_1,
                               return_bool_1]
}


pred Lista_poll_first[
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue + null
]{
  precondition_Lista_poll_first[thisType_1_0]
  and 
  postcondition_Lista_poll_first[thisType_1_0,
                                thisType_1_1,
                                return_intJ_1_1]
}


pred Lista_indexOf[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_indexOf[]
  and 
  postcondition_Lista_indexOf[intJ_1_0,
                             thisType_1_0,
                             thisType_1_1,
                             return_intJ_1_1]
}


pred verify_null[
  s_0: JavaPrimitiveIntegerValue,
  b_1: boolean
]{
  TruePred[]
  and 
  pos_add_null[s_0,
              b_1]
}
one sig QF {
  ac_1: actionExec,
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  intJ_2_0: JavaPrimitiveIntegerValue,
  intJ_2_1: JavaPrimitiveIntegerValue,
  return_bool_0: boolean,
  return_bool_1: boolean,
  return_intJ_1_0: JavaPrimitiveIntegerValue + null,
  return_intJ_1_1: JavaPrimitiveIntegerValue + null,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  valid_bool_1: boolean,
  valid_bool_2: boolean,
  valid_intA_1: boolean,
  valid_intJ_1: boolean,
  valid_intJ_2: boolean
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
  (
    (
      (
        (
          (
            (
              (
                TS_size[QF.return_intJ_1_1,
                       QF.thisType_1_0,
                       QF.thisType_1_1]
                and 
                (
                  QF.ac_1=TS_size)
                and 
                verify_null[QF.return_intJ_1_1,
                           QF.valid_intJ_2]
              )
              or 
              (
                Lista_pop[QF.thisType_1_0,
                         QF.thisType_1_1,
                         QF.return_intJ_1_1]
                and 
                (
                  QF.ac_1=Lista_pop)
                and 
                verify_null[QF.return_intJ_1_1,
                           QF.valid_intJ_2]
              )
              
              or 
              (
                get_first[QF.return_intJ_1_1,
                         QF.thisType_1_0,
                         QF.thisType_1_1]
                and 
                (
                  QF.ac_1=get_first)
                and 
                verify_null[QF.return_intJ_1_1,
                           QF.valid_intJ_2]
              )
            )
            and 
            (
              QF.intJ_1_0=QF.intJ_1_1)
          )
          or 
          (
            gen_intJ[QF.intJ_1_1]
            and 
            Lista_last_indexOf[QF.intJ_1_1,
                              QF.thisType_1_0,
                              QF.thisType_1_1,
                              QF.return_intJ_1_1]
            and 
            (
              QF.ac_1=Lista_last_indexOf)
            and 
            verify_null[QF.return_intJ_1_1,
                       QF.valid_intJ_2]
          )
          
          or 
          (
            Lista_element_m[QF.return_intJ_1_1,
                           QF.thisType_1_0,
                           QF.thisType_1_1]
            and 
            (
              QF.ac_1=Lista_element_m)
            and 
            verify_null[QF.return_intJ_1_1,
                       QF.valid_intJ_2]
            and 
            (
              QF.intJ_1_0=QF.intJ_1_1)
          )
          
          or 
          (
            gen_intJ[QF.intJ_1_1]
            and 
            add[QF.intJ_1_1,
               QF.thisType_1_0,
               QF.thisType_1_1]
            and 
            (
              QF.ac_1=add)
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
            and 
            (
              QF.valid_intJ_1=QF.valid_intJ_2)
          )
          
          or 
          (
            Lista_remove_last[QF.thisType_1_0,
                             QF.thisType_1_1,
                             QF.return_intJ_1_1]
            and 
            (
              QF.ac_1=Lista_remove_last)
            and 
            verify_null[QF.return_intJ_1_1,
                       QF.valid_intJ_2]
            and 
            (
              QF.intJ_1_0=QF.intJ_1_1)
          )
        )
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      or 
      (
        gen_intJ[QF.intJ_1_1]
        and 
        Lista_remove_fo[QF.intJ_1_1,
                       QF.thisType_1_0,
                       QF.thisType_1_1,
                       QF.return_bool_1]
        and 
        (
          QF.ac_1=Lista_remove_fo)
        and 
        (
          QF.valid_bool_2=true)
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.valid_intJ_1=QF.valid_intJ_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_1]
        and 
        Lista_indexOf[QF.intJ_1_1,
                     QF.thisType_1_0,
                     QF.thisType_1_1,
                     QF.return_intJ_1_1]
        and 
        (
          QF.ac_1=Lista_indexOf)
        and 
        verify_null[QF.return_intJ_1_1,
                   QF.valid_intJ_2]
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_1]
        and 
        Lista_get[QF.return_intJ_1_1,
                 QF.intJ_1_1,
                 QF.thisType_1_0,
                 QF.thisType_1_1]
        and 
        (
          QF.ac_1=Lista_get)
        and 
        verify_null[QF.return_intJ_1_1,
                   QF.valid_intJ_2]
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_1]
        and 
        Lista_remove_m[QF.intJ_1_1,
                      QF.thisType_1_0,
                      QF.thisType_1_1,
                      QF.return_intJ_1_1]
        and 
        (
          QF.ac_1=Lista_remove_m)
        and 
        verify_null[QF.return_intJ_1_1,
                   QF.valid_intJ_2]
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        Lista_poll[QF.thisType_1_0,
                  QF.thisType_1_1,
                  QF.return_intJ_1_1]
        and 
        (
          QF.ac_1=Lista_poll)
        and 
        verify_null[QF.return_intJ_1_1,
                   QF.valid_intJ_2]
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.intJ_1_0=QF.intJ_1_1)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
    )
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  or 
  (
    gen_intJ[QF.intJ_1_1]
    and 
    gen_intJ[QF.intJ_2_1]
    and 
    Lista_set_element[QF.intJ_1_1,
                     QF.intJ_2_1,
                     QF.thisType_1_0,
                     QF.thisType_1_1,
                     QF.return_intJ_1_1]
    and 
    (
      QF.ac_1=Lista_set_element)
    and 
    verify_null[QF.return_intJ_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
  )
  
  or 
  (
    gen_intJ[QF.intJ_1_1]
    and 
    Lista_offerFirst[QF.intJ_1_1,
                    QF.thisType_1_0,
                    QF.thisType_1_1,
                    QF.return_bool_1]
    and 
    (
      QF.ac_1=Lista_offerFirst)
    and 
    (
      QF.valid_bool_2=true)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    gen_intJ[QF.intJ_1_1]
    and 
    Lista_add_last[QF.intJ_1_1,
                  QF.thisType_1_0,
                  QF.thisType_1_1]
    and 
    (
      QF.ac_1=Lista_add_last)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    gen_intJ[QF.intJ_1_1]
    and 
    Lista_offer[QF.intJ_1_1,
               QF.thisType_1_0,
               QF.thisType_1_1,
               QF.return_bool_1]
    and 
    (
      QF.ac_1=Lista_offer)
    and 
    (
      QF.valid_bool_2=true)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    Lista_getLast[QF.thisType_1_0,
                 QF.return_intJ_1_1]
    and 
    (
      QF.ac_1=Lista_getLast)
    and 
    verify_null[QF.return_intJ_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
    and 
    (
      QF.thisType_1_0=QF.thisType_1_1)
  )
  
  or 
  (
    Lista_poll_first[QF.thisType_1_0,
                    QF.thisType_1_1,
                    QF.return_intJ_1_1]
    and 
    (
      QF.ac_1=Lista_poll_first)
    and 
    verify_null[QF.return_intJ_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    TS_clear_0[QF.thisType_1_0,
              QF.thisType_1_1]
    and 
    (
      QF.ac_1=TS_clear_0)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    Lista_poll_last[QF.thisType_1_0,
                   QF.thisType_1_1,
                   QF.return_intJ_1_1]
    and 
    (
      QF.ac_1=Lista_poll_last)
    and 
    verify_null[QF.return_intJ_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    gen_intJ[QF.intJ_1_1]
    and 
    Lista_offer_last[QF.intJ_1_1,
                    QF.thisType_1_0,
                    QF.thisType_1_1,
                    QF.return_bool_1]
    and 
    (
      QF.ac_1=Lista_offer_last)
    and 
    (
      QF.valid_bool_2=true)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    gen_intJ[QF.intJ_1_1]
    and 
    contains[QF.return_bool_1,
            QF.intJ_1_1,
            QF.thisType_1_0,
            QF.thisType_1_1]
    and 
    (
      QF.ac_1=contains)
    and 
    (
      QF.valid_bool_2=true)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    Listaremove_first[QF.thisType_1_0,
                     QF.thisType_1_1,
                     QF.return_intJ_1_1]
    and 
    (
      QF.ac_1=Listaremove_first)
    and 
    verify_null[QF.return_intJ_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    Lista_peekLast[QF.thisType_1_0,
                  QF.return_intJ_1_1]
    and 
    (
      QF.ac_1=Lista_peekLast)
    and 
    verify_null[QF.return_intJ_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
    and 
    (
      QF.thisType_1_0=QF.thisType_1_1)
  )
  
  or 
  (
    gen_intJ[QF.intJ_1_1]
    and 
    gen_intJ[QF.intJ_2_1]
    and 
    Lista_add2[QF.intJ_1_1,
              QF.intJ_2_1,
              QF.thisType_1_0,
              QF.thisType_1_1]
    and 
    (
      QF.ac_1=Lista_add2)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
  )
  
  or 
  (
    gen_intJ[QF.intJ_1_1]
    and 
    Lista_remove2[QF.intJ_1_1,
                 QF.thisType_1_0,
                 QF.thisType_1_1,
                 QF.return_bool_1]
    and 
    (
      QF.ac_1=Lista_remove2)
    and 
    (
      QF.valid_bool_2=true)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    peek[QF.return_intJ_1_1,
        QF.thisType_1_0,
        QF.thisType_1_1]
    and 
    (
      QF.ac_1=peek)
    and 
    verify_null[QF.return_intJ_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    peek_first[QF.return_intJ_1_1,
              QF.thisType_1_0,
              QF.thisType_1_1]
    and 
    (
      QF.ac_1=peek_first)
    and 
    verify_null[QF.return_intJ_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    gen_intJ[QF.intJ_1_1]
    and 
    Lista_push[QF.intJ_1_1,
              QF.thisType_1_0,
              QF.thisType_1_1]
    and 
    (
      QF.ac_1=Lista_push)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    Lista_isEmpty[QF.return_bool_1,
                 QF.thisType_1_0,
                 QF.thisType_1_1]
    and 
    (
      QF.ac_1=Lista_isEmpty)
    and 
    (
      QF.valid_bool_2=true)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )
  
  or 
  (
    Listaremove[QF.thisType_1_0,
               QF.thisType_1_1,
               QF.return_intJ_1_1]
    and 
    (
      QF.ac_1=Listaremove)
    and 
    verify_null[QF.return_intJ_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_1)
  )

}

assert programa_wap{
  pred_not[QF.intJ_1_0,
          QF.thisType_1_0,
          QF.thisType_1_1]
}
/*INI_PRE*/fact{QF.thisType_1_0 in ( i320->i32100)+( i321->i32200)+( i322->i32300) and ( i320->i32100)+( i321->i32200)+( i322->i32300) in QF.thisType_1_0}  one sig i32m1  extends JavaPrimitiveIntegerValue{}  one sig i320  extends JavaPrimitiveIntegerValue{}  one sig i321  extends JavaPrimitiveIntegerValue{}  one sig i322  extends JavaPrimitiveIntegerValue{}  one sig i323  extends JavaPrimitiveIntegerValue{}  one sig i324  extends JavaPrimitiveIntegerValue{}  one sig i32100  extends JavaPrimitiveIntegerValue{}  one sig i32200  extends JavaPrimitiveIntegerValue{}  one sig i32300  extends JavaPrimitiveIntegerValue{}  fact{ b00 in i32m1->true  + i320->false  + i321->true  + i322->false  + i323->true  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->true  + i322->false  + i323->true  + i324->false  + i32100->false  + i32200->false  + i32300->false  in  b00 and  b01 in i32m1->true  + i320->false  + i321->false  + i322->true  + i323->true  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->true  + i323->true  + i324->false  + i32100->false  + i32200->false  + i32300->false  in  b01 and  b02 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->true  + i32100->true  + i32200->false  + i32300->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->true  + i32100->true  + i32200->false  + i32300->true  in  b02 and  b03 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->true  + i32300->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->true  + i32300->true  in  b03 and  b04 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in  b04 and  b05 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->true  + i32200->false  + i32300->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->true  + i32200->false  + i32300->true  in  b05 and  b06 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->true  + i32200->true  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->true  + i32200->true  + i32300->false  in  b06 and  b07 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->true  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->true  + i32300->false  in  b07 and  b08 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->true  in  b08 and  b09 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in  b09 and b10 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b10 and b11 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b11 and b12 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b12 and b13 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b13 and b14 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b14 and b15 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b15 and b16 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b16 and b17 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b17 and b18 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b18 and b19 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b19 and b20 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b20 and b21 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b21 and b22 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b22 and b23 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b23 and b24 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b24 and b25 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b25 and b26 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b26 and b27 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b27 and b28 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b28 and b29 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b29 and b30 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b30 and b31 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i32100->false  + i32200->false  + i32300->false  in b31} fact { QF.intJ_1_0=i320}  check programa_wap for 0 but 11 JavaPrimitiveIntegerValue  fun int32_max[es: set (i320+i321+i322+i323)] : lone (i320+i321+i322+i323) { es - es.(   i321->(i320)   +   i322->(i320+i321)   +   i323->(i320+i321+i322) )}fun int32_prevs[e: i320+i321+i322+i323] :set (i320+i321+i322+i323) { e.(   i321->(i320)   +   i322->(i320+i321)   +   i323->(i320+i321+i322) )}pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {	let dom = s.JavaPrimitiveIntegerValue |		(no dom and res = i320) or 		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])}/*FIN_PRE*/
