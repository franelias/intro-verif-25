<a href='https://codespaces.new/mtzguido/intro-verif-25' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

# Introducción a la Verificación Formal

**Información de la materia:**
[aquí](https://mtzguido.github.io/teaching/ivf25/index.html)

Para instrucciones sobre cómo correr F* ver: [Ejecutar.md](./Ejecutar.md).

Para instrucciones sobre cómo usar la extensión, ver
[aquí](https://github.com/FStarLang/fstar-vscode-assistant?tab=readme-ov-file#basic-navigation).

## Trabajo Final

El trabajo final consta de la implementación de un Ternary Search Tree, estructura que almacena palabras y permite realizar búsquedas.

Se define como tipo de la forma
```
| N (l, m, r, c, w)
| L
```

en la que N representa un nodo que almacena el carácter `c`, `l` y `r` los hijos del árbol cuyos nodos son menores y mayores respectivamente, `m` el hijo que indica que sigue con el resto de la palabra y `w` que indica si una palabra termina en el nodo.

### Invariante

El invariante `is_tst` exige lo siguiente en cada nodo:
- Se mantiene el orden de un BST: en un nodo `N (l, m, r, c, w)`, todos los caracteres del árbol `l` son menores que `c` y todos los del árbol `r` son mayores (siguiendo el criterio de la función `int_of_char`).
- No hay nodos muertos: cada nodo termina en una palabra o tiene continuación. Con cada `delete` se hace un `prune` del resultado, de manera de que no queden nodos sin hijos en el árbol del medio para optimizar la búsqueda en el árbol.

Adicionalmente, el árbol no tiene representación para los strings vacíos.

### Operaciones

Se implementan tres operaciones:
- `insert t s`: inserta la palabra `s` en el árbol `t`. Si `s` es vacía, se retorna el mismo `t`.
- `delete t s`: borra la palabra `s` del árbol `t`. En cada recursión prunea el árbol, de manera de no dejar nodos muertos.
- `lookup t s`: retorna `true` o `false` si la palabra `s` está o no en el árbol `t`.

### Pruebas

Se prueban tres propiedades:
- Las operaciones `insert` y `delete` preservan el invariante (lemas `insert0_tst` y `delete0_tst`).
- La operación `lookup` es correcta.
- La estructura se comporta como un conjunto: se da una implementación de `Container`, la relación `models t ss` y se prueban las leyes de `container_laws`.

### Estructura

El proyecto tiene tres archivos de interés:
- `TST.fst`: define la estructura del árbol y las operaciones, junto con la prueba de que preservan el invariante. El árbol se define como un tipo `tst0` y luego se refina con el invariante.
- `TST2.fst`: contiene la prueba de correctitud de `lookup`, comparando el resultado con una búsqueda ineficiente en el árbol.
- `TST3.fst`: da la prueba de que TST se comporta como un conjunto. Define la instancia de `container0`, la función `models` para este caso y la instancia de `container_laws`.
