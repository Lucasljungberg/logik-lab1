% Lab 1 in Logic in Computer Science course
% Authors:
%           Lucas Ljungberg <lucaslj@kth.se>
%           Anton Ronsjö    <ronsjo@kth.se>
%

%% Startpoint of the program.
verify(InputFileName) :-
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    valid_goal(Goal, Proof),
    valid_proof(Prems, Proof, Proof, []), !.

valid_goal(Goal, Proof) :-
    get_last(Proof, Row),
    get_value(Row, Value),
    Goal = Value, !.

valid_premise(_, []):- fail.
valid_premise(Value, [Value | _]).
valid_premise(Value, [_ | Tail]) :- valid_premise(Value, Tail).

get_first([Head | _], Head).
get_last([Head | []], Head).
get_last([_| Tail], Head) :- get_last(Tail, Head).

get_value([_, Head, _], Head).
get_nr([Nr, _, _], Nr).

box_in_scope(_, [], _) :- fail.
box_in_scope([Nr, Value, _], [[[Nr, Value, _] | BoxTail] | _], [[Nr, Value, _] | BoxTail]).
box_in_scope([Nr, Value, _], [ _ | Tail], Box) :- 
    box_in_scope([Nr, Value, _], Tail, Box).

peek(_, [], _) :- fail.
peek(Nr, [[Nr, Value, _] | _], Value).
peek(Nr, [_ | Tail], Row) :- peek(Nr, Tail, Row).       

valid_proof(_, _, [], _) :- !.

valid_proof(Prems, Proof, [[[Row, Value, assumption] | BoxTail] | Tail], Scope) :-
    valid_proof(Prems, Proof, BoxTail, [[Row, Value, assumption] | Scope]),
    valid_proof(Prems, Proof, Tail, [[[Row, Value, assumption] | BoxTail] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, premise] | Tail], Scope) :-
    valid_premise(Value, Prems),
    valid_proof(Prems, Proof, Tail, [[Row, Value, premise] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, impel(X,Y)] | Tail], Scope) :-
    peek(X, Scope, Copy1),
    peek(Y, Scope, imp(Copy1, Value)),
    valid_proof(Prems, Proof, Tail, [[Row, Value, impel(X,Y)] | Scope]).

valid_proof(Prems, Proof, [[Row, imp(A,B), impint(X,Y)] | Tail], Scope) :-
    box_in_scope([X, A, _], Scope, Box),
    get_first(Box, [X, A, _]),
    get_last(Box, [Y, B, _]),
    valid_proof(Prems, Proof, Tail, [[Row, imp(A,B), impint(X,Y)] | Scope]).

valid_proof(Prems, Proof, [[Row, and(A,B), andint(X,Y)] | Tail], Scope) :-
    peek(X, Scope, A),
    peek(Y, Scope, B),
    valid_proof(Prems, Proof, Tail, [[Row, and(A,B), andint(X,Y)] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, andel1(X)] | Tail], Scope) :-
    peek(X, Scope, and(Value, _a)),
    valid_proof(Prems, Proof, Tail, [[Row, Value, andel1(X)] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, andel2(X)] | Tail], Scope) :-
    peek(X, Scope, and(_a, Value)),
    valid_proof(Prems, Proof, Tail, [[Row, Value, andel2(X)] | Scope]).

valid_proof(Prems, Proof, [[Row, or(A,B), orint1(X)] | Tail], Scope) :-
    peek(X, Scope, A),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint1(X)] | Scope]).

valid_proof(Prems, Proof, [[Row, or(A,B), orint2(X)] | Tail], Scope) :-
    peek(X, Scope, B),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint2(X)] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, orel(R, A, B, X, Y)] | Tail], Scope) :- 
    peek(R, Scope, or(P,Q)),
    box_in_scope([A, P, _], Scope, Box1),
    box_in_scope([X, Q, _], Scope, Box2),
    get_first(Box1, [A, P, _]),
    get_first(Box2, [X, Q, _]),
    get_last(Box1, [B, Value, _]),
    get_last(Box2, [Y, Value, _]),
    valid_proof(Prems, Proof, Tail, [[Row, Value, orel(R, R, B, X, Y)] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, copy(X)] | Tail], Scope) :-
    peek(X, Scope, Value),
    valid_proof(Prems, Proof, Tail, [[Row, Value, copy(X)] | Scope]).

valid_proof(Prems, Proof, [[Row, neg(A), negint(X,Y)] | Tail], Scope) :-
    box_in_scope([X, A, _], Scope, Box),
    get_first(Box, [X, A, _]),
    get_last(Box, [Y, cont, _]),
    valid_proof(Prems, Proof, Tail, [[Row, neg(A), negint(X,Y)] | Scope]).

valid_proof(Prems, Proof, [[Row, cont, negel(X,Y)] | Tail], Scope) :-
    peek(X, Scope, A),
    peek(Y, Scope, neg(A)),
    valid_proof(Prems, Proof, Tail, [[Row, cont, negel(X,Y)] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, contel(X)] | Tail], Scope) :-
    peek(X, Scope, cont),
    valid_proof(Prems, Proof, Tail, [[Row, Value, contel(X)] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, negnegint(X)] | Tail], Scope) :-
    peek(X, Scope, Copy), neg(neg(Copy)) = Value,
    valid_proof(Prems, Proof, Tail, [[Row, Value, negnegint(X)] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, negnegel(X)] | Tail], Scope) :-
    peek(X, Scope, neg(neg(Value))), 
    valid_proof(Prems, Proof, Tail, [[Row, Value, negnegel(X)] | Scope]).

valid_proof(Prems, Proof, [[Row, neg(Value), mt(X,Y)] | Tail], Scope) :-
    peek(X, Scope, imp(Value,B)),
    peek(Y, Scope, neg(B)),
    valid_proof(Prems, Proof, Tail, [[Row, neg(Value), mt(X,Y)] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, pbc(X, Y)] | Tail], Scope) :-
    box_in_scope([X, neg(Value), _], Scope, Box),
    get_first(Box, [X, neg(Value), _]),
    get_last(Box, [Y, cont, _]),
    valid_proof(Prems, Proof, Tail, [[Row, Value, pbc(X,Y)] | Scope]). 

valid_proof(Prems, Proof, [[Row, or(A, B), lem] | Tail], Scope) :-
    A = neg(B) ; B = neg(A),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), lem] | Scope]).