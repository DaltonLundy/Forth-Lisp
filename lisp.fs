( ------ misc ----------- )
: 3dup  2 pick 2 pick 2 pick ;
: 3drop drop drop drop ;

( ----- lists and their words ----- )

: allocateNode ( addr )        2 cells allocate throw ;
: emptyNode ( addr )           allocateNode 0 over ! 0 over cell+ ! ;
: isEmpty  ( node -- bool )    dup @ 0= swap cell+ @ 0= and ;
: isNotEmpty  ( node -- bool ) dup @ 0<> swap cell+ @ 0<> or ;
: toNode ( addr -- node )      emptyNode 2dup ! nip ;
: stack ( list addr -- list )  toNode 2dup cell+ ! nip ;
: pop   ( list -- list addr )  dup @ swap  cell+ @ swap  ;
: nextNode ( list -- list )    dup isNotEmpty if cell+ @ endif ;
: lastNode ( list -- node )    dup isNotEmpty if begin dup cell+ @ isNotEmpty while nextNode repeat endif ;
: appendNode ( list addr -- list )   
                                    toNode over dup isNotEmpty if 
                                     lastNode nextNode over cell+ ! swap dup >r lastNode cell+ ! r>
                                    else
                                   ( emptylist newnode emptylist )
                                   over cell+ ! nip endif ;
: nextNode2  ( node1 node2 -- node3 node4 ) nextnode swap nextnode swap ;
: deleteNode ( list idx  -- )
	1- 
	swap dup nextnode 2>r
	begin 
	dup while
		2r> dup isEmpty if abort endif nextnode2 2>r 1-
	repeat
	drop
	2r> nextnode swap cell+ ! 
;

: isOneNode ( list -- bool ) nextnode isEmpty ;

( --- String parsing gen words --- )
: packString ( addr n -- addr )               2 cells allocate throw dup >r ! r> dup >r cell+ ! r> ;
: unPackString ( addr -- addr n )             dup cell+ @ swap @ ;
: nextChar  ( addr n -- addr' n' )            1- swap 1+ swap  ;
: currentChar  ( addr len -- addr len char )  over c@ ;
: isLParen     ( char -- bool )               40 = ;
: isRParen     ( char -- bool )               41 = ;
: isLower      ( char -- bool )               dup 123 <  swap 96 >  and ;
: isUpper      ( char -- bool )               dup 91  <  swap 64 >  and ;
: isAlpha      ( char -- bool )               dup isUpper swap isLower or ;
: isNum        ( char -- bool )               dup 58 < swap 47 > and ;
: isStrQuote   ( char -- bool )               34 = ;
: ischarQuote  ( char -- bool )               39 = ;
: isAtomic     ( char -- bool )               dup isAlpha swap isNum or ;
: isSemiColon  ( char -- bool )               59 = ;
: isSpace      ( char -- bool )               32 = ;
: isTic        ( char -- bool )               96 = ;
: getParen_cond ( addr len accum -- addr len accum bool )  rot dup c@ isRParen if 
                                                                     -rot dup 0<> 
                                                                    else
                                                                     -rot over 0 >
                                                                     endif
;
: getParen_    ( addr len accum -- addr len ) begin getParen_cond while 
                                              >r 
                                              over c@ isLParen if
                                                  r> 1+ >r
                                              endif
                                              over c@ isRParen if
                                                  r> 1- >r
                                              endif
                                              nextChar r> repeat
                                              drop 
                                              dup 0 < if 
                                                    s" getParen_ error " type cr .s cr abort
                                              endif
;

: getParen ( addr len -- addr len )           0 getParen_ ;
: skipSpace ( addr len -- addr len )          32 skip ;
: skipTab   ( addr len -- addr len )          9  skip ;
: skipSpaces ( addr len -- addr len )         skipTab skipSpace ;
: nextStrQuote ( addr len -- addr len )       begin 
                                              dup -1 > if over c@ isStrQuote 0= else 0 endif while 
                                              nextChar repeat ;

( --- Atoms --- )
1 Constant AtomFlag
: allocateAtom ( atom )          cell 1+ allocate throw ;
: mkAtom  ( addr len -- addr ) packString allocateAtom AtomFlag over c! 2dup 1+ ! nip  ;
: parseAtom ( addr len -- addr len atom ) 2dup 
                                          begin over c@ isAtomic while nextChar repeat 
                                          ( OGList OGLen newList newLen )
                                           swap ( OGList OGLen newLen newList )
                                           >r   ( OGList OGLen newLen )
                                           dup >r ( OGList OGLen newLen )
                                           -     ( OGList difflen ) 
                                           mkAtom ( atom )
                                           r> r>    ( Atom newLen newList )
                                           swap     ( Atom newList newLen )
                                           rot      ( newList newLen Atom )
;

: unPackAtom ( addr -- addr len )   1+ @  dup cell+ @  swap @  ;
: copyAtom ( addr1 -- addr2 )  unpackAtom  save-mem  mkAtom ;

( --- lisp lists --- )
2 Constant ListFlag 
: allocateLispList ( addr ) cell 1+ allocate throw ;
: mkLispList ( list -- lisplist ) allocatelispList dup ListFlag swap c! 2dup 1+ ! nip ;
: unpackLispList ( lispLIst -- list ) @ 1+ @ ;
: toList ( addr -- lispList)  emptyNode swap appendNode ;
: isNested ( List -- bool ) dup isOneNode if @ c@ ListFlag = else 0 endif ;

( --- Strings --- )
3 Constant StrFlag
: allocateString ( addr ) cell 1+ allocate throw ;
: MkString ( addr len -- addr ) mkAtom strFlag over c! ;
: unPackString_ ( addr -- addr len ) unPackAtom ;
: parseString  ( addr len -- addr len str ) 2dup nextStrQuote ( addr len newaddr newlen )
                                            swap >r           ( addr len newlen )
                                            2dup -            ( addr len newlen diff )
                                            3 roll swap       ( len newlen addr diff )
                                            mkString          ( len newlwn str )
                                            rot               ( newlen str len )
                                            drop              ( newlen str ) 
                                            r>                ( newlen str newaddr )
                                            rot               ( str newaddr newlen )
                                            rot               ( newlen newaddr str )
;

: copyStr unPackString_ save-mem MkString ;

( ----- Thunks ----- )
4 Constant ThunkFlag
: toThunk ( addr1 -- addr1 ) 1 cells 1+ allocate throw 
                             swap over 1+ ! 
                             ThunkFlag over c! ;
: unThunk ( addr1 -- addr2 ) 1+ @ ;

Defer copyLispList 

: copyItem
	  dup c@ AtomFlag = if
	    copyAtom AppendNode
	  else
	  dup c@ ListFlag = if
            1+ @ copyLispList mkLispList AppendNode
          else 
	  dup c@ thunkFlag = if
            unThunk recurse toThunk
          else 
            abort
	  endif endif endif
;

: copyLispList_ ( newlist oldlist -- newlist ) 
  begin
	  dup isEmpty 0= while
	  dup >r
	  @  copyItem
	  r>
          nextnode 
  repeat 
  drop
;

:noname emptyNode swap copyLispList_ ; is copyLispList

( --- Globals --- )
Variable return_stack
emptyNode return_stack !
: toReturnStack ( addr len -- )  packString return_stack @ swap stack return_stack ! ;
: popReturnStack ( -- addr len ) return_stack @ pop swap  >r unPackString r> return_stack ! ;

( --- Main Parsing --- )
Defer parseList_ ( list addr len -- list )
Defer parseThunk ( list addr len -- list )

: parseAtomsInList ( list addr len -- list )
	begin 

          over c@ isRParen 0=  while

                  over c@ isLParen if
		    nextchar 2dup getParen toReturnStack ( List addr len )
		     emptyNode       ( list addr len emptylist )
		     -rot            ( list emptylist addr len )
		     parseList_ mkLispList     ( list newlist ) 
		     appendNode          ( list )
		     popReturnStack  ( list addr len )
                     nextchar
                 else
  
                 over c@ isAtomic if
			 parseAtom ( list addr len atom )
			 3 roll    ( addr len atom list )
			 swap      ( addr len list atom )
			 appendNode    ( addr len list )
			 -rot      ( list addr len )
                 else
                 
                 over c@ isStrQuote if
                         nextchar
                         parseString
			 3 roll    ( addr len atom list )
			 swap      ( addr len list atom )
			 appendNode    ( addr len list )
			 -rot      ( list addr len )
                         nextchar
                 else
                 
                 over c@ isTic if
		     parseThunk      ( list addr len ) 
                     nextchar
                 else
                 nextchar 
                 endif endif endif endif
	repeat
        drop drop
;

:noname  ( list addr len -- newlist addr len )
        nextChar skipSpaces
	over c@ isLParen if 
                nextchar
	        emptyNode       ( list addr len emptylist )
	        -rot            ( list emptylist addr len )
                2dup 
                getParen
                toReturnStack ( List addr len )
		parseList_ 
                mkLispList toThunk
                appendNode
	        popReturnStack  ( list addr len )
	else 
		parseAtom toThunk >r rot r> appendNode -rot
	endif
; is ParseThunk

:noname skipSpaces parseAtomsInList ; is ParseList_

: parseList ( addr len -- list ) emptyNode -rot 40 scan nextchar parseList_ ;

( --- Serialization --- )

Variable indent
0 indent !

4 constant margins 

: increaseIndent indent @ margins + indent ! ;
: decreaseIndent indent @ margins - indent ! ;

: emitMargin indent @ 0 ?do 32 emit loop ;


: showAtom unpackAtom type ;
: showString 34 emit showAtom 34 emit ;

Defer serialize ( lisplist -- )
Defer showThunk

: showItem ( addr -- )
	     dup c@ AtomFlag = if 
                32 emit
		showAtom
		32 emit
	     else
	     dup c@ StrFlag = if 
                32 emit
		showString
		32 emit
             else
	       dup c@ ListFlag = if
                increaseIndent
                1+ @  serialize
                decreaseIndent
		32 emit
                drop
             else
	       dup c@ ThunkFlag = if
                 1+ @
                 showThunk
	   endif endif endif endif
;

:noname 
                increaseIndent
                32 emit
                96 emit
                showItem 
                decreaseIndent
		32 emit
; is ShowThunk

: serialHelper ( lisplist -- )
  begin
  dup if dup IsEmpty 0= if -1 else 0 endif endif while
	   dup @ showItem
  nextNode
  repeat
  drop
  41 emit
;

:noname ( lisplist -- )
  cr
  emitMargin 
  40 emit 
  dup
  dup isEmpty if 41 emit else 
  serialHelper endif
; is serialize


( --- Dictionaries and their words --- )

\ Dictionaries are stacks of [ pointer to packed String ; ponter to corresponding lispList ]
 : allocate-entry emptyNode ;
 : mkEntry ( lispList addr len ) packString allocate-entry swap over ! swap over cell+ ! ;
 : addEntry ( Dict lispList addr len )  mkEntry stack ;
 : EmptyDict emptyNode ;
 : lookupDict ( Dict packedStr -- lisplist/0 )
   over isEmpty if
       drop drop 0
   else
      >r pop 
       dup @ unpackString r> dup >r unpackString str= if
        rdrop cell+ @
       else drop r> recurse
       endif
   endif
 ;

variable GlobalDict
emptyNode GlobalDict !

: stackGlobalDict ( addr -- )
  GlobalDict @ swap stack 
  GlobalDict !
;

: popGlobalDict ( -- addr )
  GlobalDict @ pop 
  swap GlobalDict !
;

( ----- Eval ----- ) 

  ( -- keywords -- )
s" lambda"       packString constant lambda_KW 
s" assign"       packString constant assign_KW  
s" eval"         packString constant eval_KW   
s" call_forth"   packString constant call_Forth_KW   
s" stack_forth"  packString constant stack_Forth_KW

 emptyNode
 lambda_KW      stack
 assign_KW      stack
 eval_KW        stack
 call_Forth_KW  stack
 stack_Forth_KW stack
 constant keyword_list

: replaced_Node ( node str addr -- node/addr ) 
  >r 
  unpackString  ( node straddr len )
  rot ( straddr len node )
  
  dup >r 
  unpackAtom ( straddr len atomaddr len2 )
  str= if
    rdrop r>
  else
    r> rdrop
  endif
;

defer replace 
defer replaceItem

: replaceItem_ ( packedStr addr lisplist --  )

	  dup c@ atomFlag = if
            -rot replaced_node over ! 
          else

	  dup c@ listflag = if
            1+ @ replace 
          else 

	 dup c@ thunkflag = if
          1+ @ replaceItem
          else
          3drop
	  endif endif endif
;

:noname replaceItem_ ; is replaceItem

: replace_ (  packedStr addr lisplist -- )
  begin
  dup if dup isEmpty 0= else 0 endif while
       3dup @ replaceItem_
       nextnode 
  repeat 
  3drop 
;

:noname replace_  ; is replace

: isLambda ( lispList -- Bool ) @ unpackAtom lambda_kw unpackString str= ;
: getvarArg ( lambda -- atom ) dup isLambda if nextnode @ 1+ @ @ else abort endif ;
: introduce ( lispList -- ) dup isLambda if 
                          nextnode dup 
                          @ 1+ @ dup isEmpty if
                          else
                            pop drop mkLispList swap !
                          endif
                          else abort endif
;
: getBody  ( Lambda -- lisplist ) dup isLambda if 
                                    nextnode nextnode 
                                  else abort endif ;

: emptyArgs ( lambda -- bool )    dup isLambda if 
                                    nextNode @ 1+ @ isEmpty 
                                  else abort endif ;

: betaReduce ( arg Lambda  -- result ) 
      dup isLambda if  
      dup getvarArg unpackAtom packString ( arg lambda varstr )
               swap  ( arg varstr lambda )
               dup introduce ( arg varstr lambda )
                   -rot swap rot ( varStr arg lambda/body ) 
                   dup >r ( varStr arg lambda ) 
                   replace 
                   r> ( lambda )
                   dup emptyArgs if getBody endif 
      else 
          abort
      endif
;

: assign_ ( addr atom -- ) unpackAtom mkEntry stackGlobalDict ;

: isAssign ( lispList -- bool ) @ 
                             dup c@ atomflag = if 
                                   unpackatom s" assign" str= 
                             else 0 endif
;

: assign  ( lisplist  -- )
  dup isAssign if 
    dup nextnode @ c@ atomFlag = if
       dup  nextnode nextnode @ swap nextnode @ assign_
    else abort endif 
  else abort endif
;

s" (  assign x y ) " parseList assign
globalDict @
