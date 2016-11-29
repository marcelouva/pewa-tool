one sig Null{}

sig List{
  head:Node+Null
}

sig Node{
  value:Int,
  sigu: Node+Null
}

fun reach[l:List]:set Node{
 (l.head.*sigu)-Null

}


pred linv[l:List]{
(  l.head=Null or some n: Node | n in reach[l]  and n.sigu=Null)

}

run linv for 1 List, 3 Node, 3 int
//one sig N0 extends Node{}
//one sig N1 extends Node{}
//one sig N2 extends Node{}
