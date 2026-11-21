1. `wp(x:= 2 * x; y := x + y, y > 10) = 2 * x + y > 10`

- Solution:
```
    {{2 * x + y > 10}}
    x := 2 * x
    {{x + y > 10}}
    y := x + y;
    {{y > 10}}
```
---
2. `wp(S1, z >= 0) = true` where S1 is the following program:
```
    if x < 0 {
        z := -x;
    } else {
        z := x;
    }
```
- Solution:

```
    {{true}}
    {{true && true}}
    {{ (x < 0 ==> x <= 0) && (x >= 0 ==> x >= 0) }}
    {{ (x < 0 ==> -x >= 0) && (x >= 0 ==> x >= 0) }}
    if x < 0 {
        z := -x;
    } else {
        z := x;
    }

    {{z >= 0}}
```
---
3. `wp(S2, z <= 10) = (x >= y) ==> (x <= 10)` where S2 is the following program:

```
    if x < y {
        if y < 10 {
            z := y;
        } else {
             z:= 10;
        }
    } else {
        z := x;
    }
```
- Solution:
```
{{ (x >= y) ==> (x <= 10) }}
{{ (true) && ((x >= y) ==> (x <= 10)) }}
{{ ((x < y) ==> true) && ((x >= y) ==> (x <= 10)) }}
{{ ((x < y) ==> ( true && true )) && ((x >= y) ==> (x <= 10)) }}
{{ ((x < y) ==> ( (y < 10 ==> y <= 10) && (y >= 10 ==> 10 <= 10))) && ((x >= y) ==> (x <= 10)) }}
    if x < y {
        if y < 10 {
            z := y;
        } else {
            z:= 10;
        }
    } else {
        z := x;
    }
{{ z <= 10 }}
```
---
4. `wp(S3, y == 5) = x == 4` where S3 is the following program:

```
    x := x + 1;
    if x > 3 {
        y := x;
    } else {
        y := 0;
    }
```
- Solution:
```
    {{x == 4}}
    {{(x > 2 ==> x == 4) && x > 2}}
    {{(x > 2 ==> x == 4) && !(x <= 2)}}
    {{(x > 2 ==> x == 4) && (!(x <= 2) || false)}}
    {{(x > 2 ==> x == 4) && (x <= 2 ==> false)}}
    {{(x + 1> 3 ==> x + 1== 5) && (x + 1 <= 3 ==> false)}}
    x:= x + 1
    {{(x > 3 ==> x == 5) && (x <= 3 ==> false)}}
    {{(x > 3 ==> x == 5) && (x <= 3 ==> 0 == 5)}}
    if x > 3 {
        y := x;
    } else {
        y := 0;
    }
    {{ y == 5}}
```
---
5. `wp(z := a[x] + 2; x:= x + 1, z == 7) = a[x] == 5`
- Solution:
```
    {{a[x] == 5}}
    {{a[x] + 2 == 7}}
    z := a[x] + 2
    {{ z == 7 }}
    x:= x + 1
    {{ z == 7 }}
```
