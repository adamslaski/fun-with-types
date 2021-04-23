type False = 'f';
type True = 't';
type Bool = False | True;

// Peano numbers

type Zero = { isZero: True };
type NonZero = { isZero: False, prev: Nat };
type Nat = Zero | NonZero;

type Succ<N extends Nat> = { isZero: False, prev: N };
type Prev<N extends Succ<Nat>> = N['prev'];
type IsZero<N extends Nat> = N['isZero'];

type _0 = Zero;
type _1 = Succ<_0>;
type _2 = Succ<_1>;
type _3 = Succ<_2>;
type _4 = Succ<_3>;
type _5 = Succ<_4>;
type _6 = Succ<_5>;
type _7 = Succ<_6>;
type _8 = Succ<_7>;
type _9 = Succ<_8>;
type _10 = Succ<_9>;

type Add<A extends Nat, B extends Nat> = A extends Zero 
    ? B 
    : A extends NonZero 
    ? Add<Prev<A>, Succ<B>> 
    : never;

type Mult<A extends Nat, B extends Nat> = A extends Zero 
    ? Zero 
    : A extends NonZero 
    ? Mult<Prev<A>, B> extends infer Prod
    ? Prod extends Nat
    ? Add<B, Prod>
    : never
    : never
    : never;


type Digit = _0 | _1 | _2 | _3 | _4 | _5 | _6 | _7 | _8 | _9 | _10;
type Decimal<A extends Digit, B extends Digit> = Add<Mult<_10, A>, B>;

const _true : True = 't';
const _false : False = 'f';
const zero: Zero = { isZero: _true};

function succ<N extends Nat> (n: N): Succ<N> {
    return { isZero : _false, prev : n };
}

const one : _1 = succ(zero);
const two : _2 = succ(one);
const three : _3 = succ(two);
const four : _4 = succ(three);
const five : _5 = succ(four);
const six : _6 = succ(five);
const seven : _7 = succ(six);
const eight : _8 = succ(seven);
const nine : _9 = succ(eight);
const ten : _10 = succ(nine);

function add<A extends Nat, B extends Nat> (a:A, b:B) : Nat{
    switch (a.isZero) {
    case 't': return b;
    case 'f': 
        let ap = a as NonZero;
        return add(ap.prev, succ(b));
    }
}

const result : Add<_1, _4> = five;
const multResult : Mult<_1, _5> = eight;

function nat_to_int(n: Nat): number {
    return n.isZero === _true ?  0 : (1 + nat_to_int((n as NonZero).prev));
}

function int_to_nat(n:number): Nat {
    return n <= 0 ? zero : succ(int_to_nat(n-1)); 
}

console.log("result: ", nat_to_int(result));





type Endo<T> = (a:T) => T;
type FNat<T> = Endo<Endo<T>>; // (a -> a) -> a -> a

const fn0:FNat<any> = f => x => x;
const s: Endo<FNat<any>> = n => f => x => f (n (f) (x));

const fn1:FNat<any> = s(fn0);
const fn2:FNat<any> = s(fn1);
const fn3:FNat<any> = s(fn2);
const fn4:FNat<any> = s(fn3);

const fnplus:  (a:FNat<any>, b:FNat<any>) => FNat<any> = (m,n) => f => x => m (f) (n (f) (x));
const fntimes: (a:FNat<any>, b:FNat<any>) => FNat<any> = (m,n) => f => m(n (f));
const fnpower: (a:FNat<any>, b:FNat<any>) => FNat<any> = (m,n) => m(p => fntimes(n,p))(fn1);

const computeFNat: (a: FNat<any>) => number = a => a(s => s+1)(0);
const printFNat: (a: FNat<any>) => void = a => console.log(computeFNat(a));



printFNat(fn0);
printFNat(fn1);
printFNat(fn2);
printFNat(fn3);
printFNat(fn4);

printFNat(fnplus(fn2, fn2));
printFNat(fntimes(fn3,  fn3));
printFNat(fntimes(fn3,  fn0));
printFNat(fnpower(fn0,  fn3));
printFNat(fnpower(fn3,  fn0));
printFNat(fnpower(fn4,  fn4));
