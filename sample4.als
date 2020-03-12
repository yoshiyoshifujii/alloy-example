open util/ordering[Day]

sig Day {
    main: Person,
    sub: Person
}

abstract sig Person {
    mainDays: set Day,
    subDays: set Day
}

one sig PersonS extends Person {}
one sig PersonO extends Person {}
one sig PersonW extends Person {}

fact {
    // メインを担当する人とサブを担当する人が等しくなる日はない
    no d: Day | d.main = d.sub
    // すべての人は、メインとなる日にサブに割り当てられることはない
    all d: Day, p: Person | d in p.mainDays implies d not in p.subDays
    // dのメインがpならpのメイン担当日にdは入っている、そうじゃなければ入っていない
    all d: Day, p: Person | p in d.main implies d in p.mainDays else d not in p.mainDays
    // dのサブがpならpのサブ担当日にdは入っている、そうじゃなければ入っていない
    all d: Day, p: Person | p in d.sub implies d in p.subDays else d not in p.subDays
    // dのメイン担当者がpならpはdのサブ担当者ではない
    all d: Day, p: Person | p in d.main implies p not in d.sub
}

// すべての人の担当日数の差は1日以内
fact {
    all p1, p2: Person | #p1.(mainDays+subDays) - #p2.(mainDays+subDays) =< 1
}

// 一日目のメインはOが担当
// 二日目のメインはWが担当
// 三日目のメインはSが担当
fact {
    first.main in PersonO
    first.next.main in PersonW
    first.next.next.main in PersonS
}

// 続けて二日間メインを担当しない
fact {
    all d: (Day-last) | d.main not in (d.next.main+d.next.sub)
}

// 事例の解析(6日間コース)
run {} for 3 but 6 Day

// 事例の解析(4日間コース)
run {} for 3 but 9 Day

// 日付と担当者の関係は、担当者と日付の関係に等しい
// 図を見ればそれらしいことがわかるが、すべての場合でそうなるかを確認
assert mainEqualmainDay {
    ~mainDays = main
    ~subDays = sub
}

check mainEqualmainDay for 3 but 9 Day
