#!/usr/bin/env python3
"""
Autor: David Santiago Carrillo Salamanca
Producto didactico y comparativo de metodos de ordenamiento.


Metodos (se eligen en la columna izquierda):
    - TimSort: metodo propio, el de la presentacion.
    - Insertion Sort: metodo inferior, O(n^2) y pieza interna de TimSort.
    - Powersort: metodo superior, TimSort con una mejor regla de fusion.


Secciones (todas trabajan con el metodo elegido, menos la 7):
    1. Algoritmo base (paso a paso animado)
    2. Representacion temporal - f(x) - Grafica y tabla de datos
    3. Rendimiento (casos de entrada y modo galope)
    4. Demo: simular cantidad de valores
    5. Calidad: valida correctitud, estabilidad y Big O medido
    6. Pseudocodigo: lo ejecuta para validar que de lo mismo que el codigo
    7. Comparacion de los tres metodos


Atajos de teclado:
    1 a 7            cambiar de seccion
    Flechas          paso anterior / siguiente
    Espacio          reproducir / pausar
    Inicio / Fin     primer / ultimo paso
    F / Esc          abrir / cerrar la ficha del metodo


Ejecutar:  python ordenamiento_didactico.py
Probar:    python ordenamiento_didactico.py --prueba
"""


import math
import queue
import random
import re
import statistics
import sys
import threading
import time

try:
    import tkinter as tk
    import tkinter.font as tkfont
    from tkinter import ttk
except ImportError:      # las pruebas no necesitan ventana: se avisa solo si se va a abrir
    tk = None


# Colores de la presentacion (identidad de la Universidad Central)
AZUL_OSCURO = "#004284"
AZUL = "#3259A0"
AZUL_CLARO = "#5B9BD5"
DORADO = "#FFC000"
GRIS = "#8C8C8C"
GRIS_CLARO = "#D9D9D9"
FONDO = "#F4F6FA"
COLOR_METODO = {"Insertion Sort": DORADO, "TimSort": AZUL_OSCURO, "Powersort": AZUL_CLARO}

# Colores de apoyo de la interfaz
AZUL_PALIDO = "#BFD3EC"
TARJETA = "#FFFFFF"
TINTA = "#14233B"
TEXTO_SUAVE = "#5C6B82"
BORDE = "#E3E8F0"
BORDE_FUERTE = "#C9D2E0"
COLUMNA = "#00356B"
COLUMNA_SOBRE = "#0A4582"
COLUMNA_ACTIVA = "#14528F"
COLUMNA_TEXTO = "#B7CBE3"
CODIGO_FONDO = "#06264D"
CODIGO_LINEA = "#0E3A70"
CODIGO_NUMERO = "#6484AE"
VERDE = "#178A5B"
ROJO = "#CF3F3F"


# ---------------------------------------------------------------------------
# Implementacion de TimSort. Tiene la misma estructura que el codigo de la
# diapositiva "Implementacion en Python":
#   - calcular_minrun: tamano minimo de cada run (entre 32 y 64).
#   - contar_run: detecta un tramo ya ordenado (run) y voltea los descendentes.
#   - insercion_binaria: completa los runs cortos hasta minrun.
#   - equilibrar_pila: reglas de la pila A > B + C y B > C.
#   - fusionar: merge estable (con <=) y modo galope (MIN_GALLOP = 7).
# Todas las funciones cuentan comparaciones y movimientos en 'contador', asi
# una sola version sirve para medir, para las graficas y para el paso a paso.
# ---------------------------------------------------------------------------
MIN_GALLOP = 7


def nuevo_contador():
    # 'min_gallop' tambien se guarda aqui: el umbral del galope se va
    # adaptando durante todo el ordenamiento (sube si galopar no sirve y baja
    # si si sirve), igual que en Python.
    return {"comparaciones": 0, "comparaciones_fusion": 0, "movimientos": 0, "min_gallop": MIN_GALLOP}


def _menor(x, y, contador):
    contador["comparaciones"] += 1
    return x < y


def calcular_minrun(n):
    """Toma los 6 bits mas altos de n y suma 1 si quedan bits en 1.
    Asi n / minrun queda cerca de una potencia de 2 (fusiones parejas)."""
    r = 0
    while n >= 64:
        r |= n & 1
        n >>= 1
    return n + r


def contar_run(a, lo, n, contador):
    """Mide el run que empieza en 'lo'. Si es estrictamente descendente lo
    invierte (el 'estrictamente' es para no romper la estabilidad).
    Devuelve (largo, si_se_invirtio)."""
    if lo + 1 == n:
        return 1, False
    largo = 2
    if _menor(a[lo + 1], a[lo], contador):          # descendente
        while lo + largo < n and _menor(a[lo + largo], a[lo + largo - 1], contador):
            largo += 1
        a[lo:lo + largo] = a[lo:lo + largo][::-1]   # invertir en O(n)
        contador["movimientos"] += largo
        return largo, True
    while lo + largo < n and not _menor(a[lo + largo], a[lo + largo - 1], contador):
        largo += 1
    return largo, False


def insercion_binaria(a, lo, fin, inicio, contador):
    """Ordena a[lo:fin] sabiendo que a[lo:inicio] ya esta ordenado. La posicion
    de cada elemento se busca con busqueda binaria (pocas comparaciones)."""
    for i in range(inicio, fin):
        pivote = a[i]
        izq, der = lo, i
        while izq < der:
            medio = (izq + der) // 2
            if _menor(pivote, a[medio], contador):
                der = medio
            else:
                izq = medio + 1           # con iguales se inserta a la derecha: estable
        a[izq + 1:i + 1] = a[izq:i]
        a[izq] = pivote
        contador["movimientos"] += i - izq + 1


def _galope_derecha(clave, arr, inicio, fin, contador):
    """Primer indice k en [inicio, fin) con clave < arr[k]. Salta 1, 3, 7, 15...
    y despues hace busqueda binaria en el ultimo tramo."""
    if inicio >= fin or _menor(clave, arr[inicio], contador):
        return inicio
    ultimo, salto = 0, 1
    while inicio + salto < fin and not _menor(clave, arr[inicio + salto], contador):
        ultimo, salto = salto, salto * 2 + 1
    izq, der = inicio + ultimo + 1, min(inicio + salto, fin)
    while izq < der:
        medio = (izq + der) // 2
        if _menor(clave, arr[medio], contador):
            der = medio
        else:
            izq = medio + 1
    return izq


def _galope_izquierda(clave, arr, inicio, fin, contador):
    """Primer indice k en [inicio, fin) con arr[k] >= clave."""
    if inicio >= fin or not _menor(arr[inicio], clave, contador):
        return inicio
    ultimo, salto = 0, 1
    while inicio + salto < fin and _menor(arr[inicio + salto], clave, contador):
        ultimo, salto = salto, salto * 2 + 1
    izq, der = inicio + ultimo + 1, min(inicio + salto, fin)
    while izq < der:
        medio = (izq + der) // 2
        if _menor(arr[medio], clave, contador):
            izq = medio + 1
        else:
            der = medio
    return izq


def fusionar(a, inicio1, largo1, inicio2, largo2, contador, galope=True):
    """Fusiona dos runs vecinos. En empate gana el de la izquierda (estable).
    Si un mismo run gana MIN_GALLOP veces seguidas se pasa al modo galope."""
    antes = contador["comparaciones"]
    if galope:
        # La parte inicial del run 1 y la final del run 2 ya estan en su lugar
        k = _galope_derecha(a[inicio2], a, inicio1, inicio1 + largo1, contador)
        largo1 -= k - inicio1
        inicio1 = k
        if largo1 > 0:
            largo2 = _galope_izquierda(a[inicio1 + largo1 - 1], a, inicio2, inicio2 + largo2, contador) - inicio2
    if largo1 > 0 and largo2 > 0:
        izquierda = a[inicio1:inicio1 + largo1]
        i, j, k, fin2 = 0, inicio2, inicio1, inicio2 + largo2
        min_gallop = contador["min_gallop"] if galope else float("inf")
        while i < largo1 and j < fin2:
            seguidas1 = seguidas2 = 0
            while i < largo1 and j < fin2:                       # uno a uno
                if _menor(a[j], izquierda[i], contador):
                    a[k] = a[j]
                    j += 1
                    seguidas2 += 1
                    seguidas1 = 0
                else:
                    a[k] = izquierda[i]
                    i += 1
                    seguidas1 += 1
                    seguidas2 = 0
                k += 1
                contador["movimientos"] += 1
                if seguidas1 >= min_gallop or seguidas2 >= min_gallop:
                    break
            while i < largo1 and j < fin2:                       # modo galope
                p = _galope_derecha(a[j], izquierda, i, largo1, contador)
                a[k:k + p - i] = izquierda[i:p]
                contador["movimientos"] += p - i
                salto1 = p - i
                k += salto1
                i = p
                if i >= largo1:
                    break
                a[k] = a[j]
                k += 1
                j += 1
                contador["movimientos"] += 1
                if j >= fin2:
                    break
                p = _galope_izquierda(izquierda[i], a, j, fin2, contador)
                a[k:k + p - j] = a[j:p]
                contador["movimientos"] += p - j
                salto2 = p - j
                k += salto2
                j = p
                if j >= fin2:
                    break
                a[k] = izquierda[i]
                k += 1
                i += 1
                contador["movimientos"] += 1
                if salto1 < MIN_GALLOP and salto2 < MIN_GALLOP:
                    min_gallop += 1       # el galope no esta sirviendo: volver a uno a uno
                    break
                min_gallop = max(1, min_gallop - 1)
        a[k:k + largo1 - i] = izquierda[i:]
        contador["movimientos"] += largo1 - i
        if galope:
            contador["min_gallop"] = min_gallop
    contador["comparaciones_fusion"] += contador["comparaciones"] - antes


def _fusionar_en(a, pila, i, contador, galope, traza):
    (inicio1, largo1), (inicio2, largo2) = pila[i], pila[i + 1]
    fusionar(a, inicio1, largo1, inicio2, largo2, contador, galope)
    pila[i] = (inicio1, largo1 + largo2)
    del pila[i + 1]
    if traza is not None:
        traza.append({"tipo": "fusion", "inicio": inicio1, "medio": inicio1 + largo1 - 1,
                      "fin": inicio1 + largo1 + largo2 - 1, "pila": [r[1] for r in pila],
                      "estado": list(a)})


def equilibrar_pila(a, pila, contador, galope=True, traza=None):
    """Reglas de la pila (A, B, C son los tres runs del tope, C el ultimo):
    se fusiona mientras falle A > B + C o B > C. Asi la pila nunca pasa de
    O(log n) runs y se fusionan runs de tamano parecido."""
    while len(pila) > 1:
        m = len(pila) - 2
        largos = [r[1] for r in pila]
        if (m > 0 and largos[m - 1] <= largos[m] + largos[m + 1]) or \
                (m > 1 and largos[m - 2] <= largos[m - 1] + largos[m]):
            if largos[m - 1] < largos[m + 1]:
                m -= 1
        elif largos[m] > largos[m + 1]:
            break
        _fusionar_en(a, pila, m, contador, galope, traza)


def fusionar_todo(a, pila, contador, galope=True, traza=None):
    while len(pila) > 1:
        m = len(pila) - 2
        if m > 0 and pila[m - 1][1] < pila[m + 1][1]:
            m -= 1
        _fusionar_en(a, pila, m, contador, galope, traza)


def timsort(a, minrun=None, contador=None, galope=True, traza=None):
    """Ordena 'a' en el sitio y lo devuelve. 'minrun' se puede forzar (por
    ejemplo 4) solo para ver el paso a paso con pocos datos; si no se pasa se
    usa calcular_minrun(n), entre 32 y 64, como en Python."""
    if contador is None:
        contador = nuevo_contador()
    n = len(a)
    if n < 2:
        return a
    if minrun is None:
        minrun = calcular_minrun(n)
    pila, lo = [], 0
    while lo < n:
        largo, invertido = contar_run(a, lo, n, contador)
        natural = largo
        if largo < minrun:                       # run corto: completar
            fin = min(lo + minrun, n)
            insercion_binaria(a, lo, fin, lo + largo, contador)
            largo = fin - lo
        pila.append((lo, largo))
        if traza is not None:
            traza.append({"tipo": "run", "inicio": lo, "natural": natural, "largo": largo,
                          "invertido": invertido, "pila": [r[1] for r in pila], "estado": list(a)})
        lo += largo
        equilibrar_pila(a, pila, contador, galope, traza)
    fusionar_todo(a, pila, contador, galope, traza)
    return a


def potencia(inicio1, largo1, largo2, n):
    """Profundidad de la frontera entre dos runs vecinos en el arbol de fusion
    casi optimo (Munro y Wild, 2018). Es el powerloop de CPython."""
    a = 2 * inicio1 + largo1
    b = a + largo1 + largo2
    resultado = 0
    while True:
        resultado += 1
        if a >= n:
            a -= n
            b -= n
        elif b >= n:
            return resultado
        a <<= 1
        b <<= 1


def powersort(a, minrun=None, contador=None, galope=True, traza=None):
    """Igual que timsort(); solo cambia la regla para decidir que runs se
    fusionan: se usa la potencia de cada frontera y no los tamanos de la pila."""
    if contador is None:
        contador = nuevo_contador()
    n = len(a)
    if n < 2:
        return a
    if minrun is None:
        minrun = calcular_minrun(n)
    pila, poderes, lo = [], [], 0
    while lo < n:
        largo, invertido = contar_run(a, lo, n, contador)
        natural = largo
        if largo < minrun:
            fin = min(lo + minrun, n)
            insercion_binaria(a, lo, fin, lo + largo, contador)
            largo = fin - lo
        if pila:
            p = potencia(pila[-1][0], pila[-1][1], largo, n)
            while poderes and poderes[-1] > p:
                _fusionar_en(a, pila, len(pila) - 2, contador, galope, traza)
                poderes.pop()
            poderes.append(p)
        pila.append((lo, largo))
        if traza is not None:
            traza.append({"tipo": "run", "inicio": lo, "natural": natural, "largo": largo,
                          "invertido": invertido, "pila": [r[1] for r in pila], "estado": list(a)})
        lo += largo
    while len(pila) > 1:
        _fusionar_en(a, pila, len(pila) - 2, contador, galope, traza)
    return a


def insertion_sort(a, minrun=None, contador=None, galope=True, traza=None):
    """Inserta cada elemento en la parte ya ordenada. minrun y galope no
    aplican aqui; se reciben para llamar a los tres metodos de la misma forma."""
    if contador is None:
        contador = nuevo_contador()
    comparaciones = movimientos = 0      # variables locales: el diccionario es mucho mas lento aqui
    for i in range(1, len(a)):
        clave = a[i]
        j = i - 1
        while j >= 0:
            comparaciones += 1
            if not clave < a[j]:
                break
            a[j + 1] = a[j]
            movimientos += 1
            j -= 1
        a[j + 1] = clave
        movimientos += 1
        if traza is not None:
            traza.append({"tipo": "insercion", "posicion": j + 1, "hasta": i, "estado": list(a)})
    contador["comparaciones"] += comparaciones
    contador["movimientos"] += movimientos
    return a


def ordenar(nombre, a, minrun=None, galope=True, traza=None):
    """Ordena 'a' con el metodo 'nombre' y devuelve el contador."""
    contador = nuevo_contador()
    ALGORITMOS[nombre]["funcion"](a, minrun, contador, galope, traza)
    return contador


def traza_de(nombre, a, minrun):
    """Guarda el estado del arreglo despues de cada operacion para la pestana
    'Algoritmo base'. El primer paso de la traza es el arreglo original."""
    traza = [{"tipo": "inicio", "estado": list(a)}]
    ordenar(nombre, a, minrun, traza=traza)
    return traza


class _Elemento:
    """Elemento con clave repetible; 'pos' guarda su posicion original para
    comprobar la estabilidad. 'comparaciones' cuenta los < sin tocar el codigo."""
    comparaciones = 0

    def __init__(self, clave, pos):
        self.clave = clave
        self.pos = pos

    def __lt__(self, otro):
        _Elemento.comparaciones += 1
        return self.clave < otro.clave


def _datos_de_prueba(nombre):
    """Arreglo con claves repetidas (a veces ya ordenado o al reves)."""
    n = random.randint(0, ALGORITMOS[nombre]["max_prueba"])
    datos = [_Elemento(random.randint(0, 50), i) for i in range(n)]
    tipo = random.random()
    if tipo < 0.3:
        datos.sort(key=lambda e: e.clave)
    elif tipo < 0.5:
        datos.sort(key=lambda e: -e.clave)
    return datos


def verificar(nombre, pruebas=400, avance=None):
    """Compara contra sorted() de Python, que es estable, en 'pruebas' arreglos.
    Devuelve (correctas, estables)."""
    correctas = estables = 0
    for prueba in range(pruebas):
        datos = _datos_de_prueba(nombre)
        mio = list(datos)
        ordenar(nombre, mio)
        referencia = sorted(datos)
        if [e.clave for e in mio] == [e.clave for e in referencia]:
            correctas += 1
        if [(e.clave, e.pos) for e in mio] == [(e.clave, e.pos) for e in referencia]:
            estables += 1
        if avance:
            avance((prueba + 1) / pruebas)
    return correctas, estables


def tramos(avance, pesos):
    """Reparte una barra de progreso entre tareas de distinto costo: devuelve
    un avance(fraccion) por tarea. Si no hay barra, cada tarea recibe None."""
    if avance is None:
        return [None] * len(pesos)
    total = sum(pesos) or 1
    partes, acumulado = [], 0
    for peso in pesos:
        partes.append(lambda f, base=acumulado, peso=peso: avance((base + f * peso) / total))
        acumulado += peso
    return partes


def _aleatorio(n):
    arreglo = list(range(n))
    random.shuffle(arreglo)
    return arreglo


def _casi_ordenado(n):
    """Ordenado, pero con el 1 % de pares intercambiados al azar."""
    arreglo = list(range(n))
    for _ in range(max(1, n // 100)):
        i, j = random.randrange(n), random.randrange(n)
        arreglo[i], arreglo[j] = arreglo[j], arreglo[i]
    return arreglo


def _runs_desiguales(n):
    """Tramos ya ordenados de tamanos muy distintos: aqui se nota la regla de Powersort."""
    arreglo = []
    while len(arreglo) < n:
        largo = max(8, n >> random.randint(3, 10))
        arreglo += sorted(random.randint(0, n) for _ in range(min(largo, n - len(arreglo))))
    return arreglo


GENERADORES_TIPO_DATOS = {
    "Aleatorio": _aleatorio,
    "Casi ordenado (1 %)": _casi_ordenado,
    "Ya ordenado": lambda n: list(range(n)),
    "Orden inverso": lambda n: list(range(n, 0, -1)),
    "Runs desiguales": _runs_desiguales,
}


def medir(nombre, n, repeticiones, generador, avance=None):
    """Ordena 'repeticiones' arreglos de tamano n. Devuelve el promedio de
    comparaciones y movimientos, y el MEJOR tiempo en ms (el minimo es el que
    menos se ve afectado por otros programas que esten corriendo)."""
    suma_comp = suma_mov = 0
    mejor_ns = None
    for repeticion in range(repeticiones):
        arreglo = generador(n)
        copia = list(arreglo)
        inicio = time.perf_counter_ns()
        contador = ordenar(nombre, arreglo)
        duracion = time.perf_counter_ns() - inicio
        if arreglo != sorted(copia):
            raise RuntimeError(f"{nombre} dejó el arreglo mal ordenado")
        suma_comp += contador["comparaciones"]
        suma_mov += contador["movimientos"]
        mejor_ns = duracion if mejor_ns is None else min(mejor_ns, duracion)
        if avance:
            avance((repeticion + 1) / repeticiones)     # fuera de la zona cronometrada
    return suma_comp / repeticiones, suma_mov / repeticiones, mejor_ns / 1_000_000


MODELOS = {"n": lambda n: n, "n log n": lambda n: n * math.log2(n), "n²": lambda n: n * n}


def estimar_modelo(tamanos, valores):
    """Si f(n) crece como g(n), la razon f(n)/g(n) es casi constante. Gana el
    modelo con la menor variacion. Devuelve (modelo, {modelo: variacion})."""
    variacion = {}
    for modelo, g in MODELOS.items():
        razones = [v / g(n) for n, v in zip(tamanos, valores)]
        variacion[modelo] = statistics.pstdev(razones) / statistics.mean(razones)
    return min(variacion, key=variacion.get), variacion


def validar_calidad(nombre, avance=None):
    """Mide cada caso del metodo y compara el Big O medido contra el teorico."""
    tamanos = [1000, 2000, 4000, 8000]
    if ALGORITMOS[nombre]["limite_n"] is None:
        tamanos += [16000, 32000]
    filas = []
    tareas = [(caso, n) for caso in ALGORITMOS[nombre]["casos"] for n in tamanos]
    partes = iter(tramos(avance, [ALGORITMOS[nombre]["f_peor"](n) for _, n in tareas]))
    for etiqueta, tipo, esperado in ALGORITMOS[nombre]["casos"]:
        valores = [medir(nombre, n, 2, GENERADORES_TIPO_DATOS[tipo], next(partes))[0] for n in tamanos]
        estimado, variacion = estimar_modelo(tamanos, valores)
        filas.append({"caso": etiqueta, "tipo": tipo, "esperado": esperado, "estimado": estimado,
                      "variacion": variacion[estimado], "valores": valores})
    return tamanos, filas


def pseudocodigo_a_python(texto):
    """Traduce el pseudocodigo linea por linea. Se conservan los numeros de
    linea: las lineas FIN quedan vacias."""
    lineas = []
    for linea in texto.splitlines():
        cuerpo = linea.strip()
        if cuerpo.startswith("FIN"):
            lineas.append("")
            continue
        cuerpo = re.sub(r"^ALGORITMO (.+)$", r"def \1:", cuerpo)
        cuerpo = re.sub(r"^PARA (\w+) <- (.+) HASTA (.+) HACER$", r"for \1 in range(\2, (\3) + 1):", cuerpo)
        cuerpo = re.sub(r"^MIENTRAS (.+) HACER$", r"while \1:", cuerpo)
        cuerpo = re.sub(r"^SI (.+) ENTONCES$", r"if \1:", cuerpo)
        cuerpo = cuerpo.replace(" <- ", " = ").replace(" Y ", " and ")
        lineas.append(linea[:len(linea) - len(linea.lstrip())] + cuerpo)
    return "\n".join(lineas)


def _entorno_pseudocodigo(contador):
    """Operaciones que el pseudocodigo puede llamar."""
    return {
        "longitud": len, "minimo": min, "calcular_minrun": calcular_minrun,
        "lista_vacia": list, "agregar": list.append, "quitar_ultimo": list.pop,
        "ultimo": lambda lista: lista[-1],
        "par": lambda x, y: (x, y),
        "potencia_tope": lambda pila, largo, n: potencia(pila[-1][0], pila[-1][1], largo, n),
        "detectar_run": lambda A, lo, n: contar_run(A, lo, n, contador)[0],
        "insercion_binaria": lambda A, lo, fin, inicio: insercion_binaria(A, lo, fin, inicio, contador),
        "equilibrar_pila": lambda A, pila: equilibrar_pila(A, pila, contador),
        "fusionar_todo": lambda A, pila: fusionar_todo(A, pila, contador),
        "fusionar_tope": lambda A, pila: _fusionar_en(A, pila, len(pila) - 2, contador, True, None),
    }


def validar_pseudocodigo(nombre, pruebas=100, avance=None):
    """Ejecuta el pseudocodigo del metodo y lo compara contra el codigo real.
    Devuelve (bien_ordenados, estables, con_las_mismas_comparaciones)."""
    texto = ALGORITMOS[nombre]["pseudocodigo"]
    funcion = re.search(r"ALGORITMO (\w+)", texto).group(1)
    ordenados = estables = iguales = 0
    for prueba in range(pruebas):
        datos = _datos_de_prueba(nombre)
        entorno = _entorno_pseudocodigo(nuevo_contador())
        exec(pseudocodigo_a_python(texto), entorno)    # solo textos fijos de ALGORITMOS, no entrada del usuario
        del_pseudo = list(datos)
        _Elemento.comparaciones = 0
        entorno[funcion](del_pseudo)
        comparaciones_pseudo = _Elemento.comparaciones
        referencia = sorted(datos)
        if [e.clave for e in del_pseudo] == [e.clave for e in referencia]:
            ordenados += 1
        if [(e.clave, e.pos) for e in del_pseudo] == [(e.clave, e.pos) for e in referencia]:
            estables += 1
        if comparaciones_pseudo == _comparaciones_de(nombre, datos):
            iguales += 1
        if avance:
            avance((prueba + 1) / pruebas)
    return ordenados, estables, iguales


def _comparaciones_de(nombre, datos):
    _Elemento.comparaciones = 0
    ordenar(nombre, list(datos))
    return _Elemento.comparaciones


def miles(x, decimales=0):
    """Formato con punto de miles, como en las diapositivas (1.553.285)."""
    texto = f"{x:,.{decimales}f}"
    return texto.replace(",", "X").replace(".", ",").replace("X", ".")


# ---------------------------------------------------------------------------
# Ficha de cada metodo: es lo que muestra la columna izquierda y lo que usan
# las pestanas para saber que curvas dibujar y que validar.
# ---------------------------------------------------------------------------
_CAMINO_RUNS = """      largo <- detectar_run(A, lo, n)
      SI largo < minrun ENTONCES
         fin <- minimo(lo + minrun, n)
         insercion_binaria(A, lo, fin, lo + largo)
         largo <- fin - lo
      FIN SI
"""


ALGORITMOS = {
    "TimSort": {
        "rol": "Propio",
        "funcion": timsort,
        "limite_n": None,
        "max_prueba": 3000,
        "categorias": ["Ordenamiento por comparación", "Híbrido (inserción + mezcla)", "Adaptativo", "Estable"],
        "historia": "Lo creó Tim Peters en 2002 para la función sort de CPython y lo documentó en el archivo "
                    "listsort.txt. Joshua Bloch lo llevó a Java en 2009 (llegó con Java 7) y por eso también lo "
                    "usa Android. En 2015 un grupo del CWI (Ámsterdam) intentó verificarlo formalmente y halló un "
                    "error en las reglas de la pila. En 2018 V8 lo adoptó para Chrome y Node.js.",
        "caracteristicas": ["Detecta los tramos ya ordenados (runs)", "Invierte los runs descendentes en O(n)",
                            "Completa los runs cortos hasta minrun (32 a 64)",
                            "Pila con las reglas A > B + C y B > C", "Modo galope al fusionar (MIN_GALLOP = 7)"],
        "big_o": {"Mejor": "Θ(n)", "Promedio": "Θ(n log n)", "Peor": "Θ(n log n)", "Espacio": "O(n)"},
        "estable": "Sí", "adaptativo": "Sí",
        "f_mejor": lambda n: max(n - 1, 0),
        "f_peor": lambda n: n * math.log2(n) if n else 0,
        "texto_mejor": "n - 1", "texto_peor": "n·log2(n)",
        "casos": [("Mejor", "Ya ordenado", "n"), ("Mejor", "Orden inverso", "n"),
                  ("Promedio y peor", "Aleatorio", "n log n")],
        "pseudocodigo": """ALGORITMO TimSort(A)
   n <- longitud(A)
   minrun <- calcular_minrun(n)
   pila <- lista_vacia()
   lo <- 0
   MIENTRAS lo < n HACER
""" + _CAMINO_RUNS + """      agregar(pila, par(lo, largo))
      lo <- lo + largo
      equilibrar_pila(A, pila)
   FIN MIENTRAS
   fusionar_todo(A, pila)
FIN ALGORITMO""",
    },
    "Insertion Sort": {
        "rol": "Inferior",
        "funcion": insertion_sort,
        "limite_n": 10000,     # shortcut: con n > 10.000 tarda minutos en Python puro, subirlo solo con mas tiempo de espera
        "max_prueba": 200,
        "categorias": ["Ordenamiento por comparación", "Incremental", "Adaptativo", "Estable", "En el sitio"],
        "historia": "Es uno de los métodos más antiguos: es lo que hacemos al ordenar cartas en la mano. Knuth "
                    "(The Art of Computer Programming, vol. 3) registra que John Mauchly ya habló de la inserción "
                    "binaria en 1946. Hoy casi no se usa solo, pero sigue vivo dentro de métodos híbridos: "
                    "TimSort y Powersort lo usan para completar los runs cortos.",
        "caracteristicas": ["Toma cada elemento y lo inserta en la parte ya ordenada",
                            "Muy simple y sin memoria extra", "Rápido con pocos datos o casi ordenados",
                            "Inútil con muchos datos: crece como n²"],
        "big_o": {"Mejor": "Θ(n)", "Promedio": "Θ(n²)", "Peor": "Θ(n²)", "Espacio": "O(1)"},
        "estable": "Sí", "adaptativo": "Sí",
        "f_mejor": lambda n: max(n - 1, 0),
        "f_peor": lambda n: n * (n - 1) / 2,
        "texto_mejor": "n - 1", "texto_peor": "n(n-1)/2",
        "casos": [("Mejor", "Ya ordenado", "n"), ("Promedio", "Aleatorio", "n²"), ("Peor", "Orden inverso", "n²")],
        "pseudocodigo": """ALGORITMO InsertionSort(A)
   n <- longitud(A)
   PARA i <- 1 HASTA n - 1 HACER
      clave <- A[i]
      j <- i - 1
      MIENTRAS j >= 0 Y A[j] > clave HACER
         A[j + 1] <- A[j]
         j <- j - 1
      FIN MIENTRAS
      A[j + 1] <- clave
   FIN PARA
FIN ALGORITMO""",
    },
    "Powersort": {
        "rol": "Superior",
        "funcion": powersort,
        "limite_n": None,
        "max_prueba": 3000,
        "categorias": ["Ordenamiento por comparación", "Híbrido (inserción + mezcla)", "Adaptativo", "Estable"],
        "historia": "Lo publicaron J. Ian Munro y Sebastian Wild en 2018 (Nearly-Optimal Mergesorts, ESA 2018). "
                    "Conserva todo TimSort y cambia solo la regla para decidir qué runs fusionar. Desde Python 3.11 "
                    "(2022) CPython usa esta regla en lugar de las reglas de la pila.",
        "caracteristicas": ["Mismas piezas que TimSort: runs, minrun y galope",
                            "Decide las fusiones con la 'potencia' de cada frontera",
                            "Costo de fusión casi óptimo: n·H + 2n, donde H es la entropía de los runs",
                            "Con datos aleatorios empata con TimSort",
                            "Gana cuando hay runs de tamaños desiguales (sección 7)"],
        "big_o": {"Mejor": "Θ(n)", "Promedio": "Θ(n log n)", "Peor": "Θ(n log n)", "Espacio": "O(n)"},
        "estable": "Sí", "adaptativo": "Sí",
        "f_mejor": lambda n: max(n - 1, 0),
        "f_peor": lambda n: n * math.log2(n) if n else 0,
        "texto_mejor": "n - 1", "texto_peor": "n·log2(n)",
        "casos": [("Mejor", "Ya ordenado", "n"), ("Mejor", "Orden inverso", "n"),
                  ("Promedio y peor", "Aleatorio", "n log n")],
        "pseudocodigo": """ALGORITMO Powersort(A)
   n <- longitud(A)
   minrun <- calcular_minrun(n)
   pila <- lista_vacia()
   poderes <- lista_vacia()
   lo <- 0
   MIENTRAS lo < n HACER
""" + _CAMINO_RUNS + """      SI longitud(pila) > 0 ENTONCES
         p <- potencia_tope(pila, largo, n)
         MIENTRAS longitud(poderes) > 0 Y ultimo(poderes) > p HACER
            fusionar_tope(A, pila)
            quitar_ultimo(poderes)
         FIN MIENTRAS
         agregar(poderes, p)
      FIN SI
      agregar(pila, par(lo, largo))
      lo <- lo + largo
   FIN MIENTRAS
   MIENTRAS longitud(pila) > 1 HACER
      fusionar_tope(A, pila)
   FIN MIENTRAS
FIN ALGORITMO""",
    },
}


# ---------------------------------------------------------------------------
# Pruebas: antes estaban en un archivo aparte. Se corren sin abrir la ventana.
# ---------------------------------------------------------------------------
def correr_pruebas():
    for nombre in ALGORITMOS:
        assert verificar(nombre, 100) == (100, 100), nombre
        assert validar_pseudocodigo(nombre, 30) == (30, 30, 30), nombre
        tamanos, filas = validar_calidad(nombre)
        for fila in filas:
            assert fila["estimado"] == fila["esperado"], (nombre, fila["tipo"], fila["estimado"])
        traza = traza_de(nombre, [5, 1, 4, 2, 3, 9, 8], 2)
        assert traza[-1]["estado"] == [1, 2, 3, 4, 5, 8, 9], nombre

    # Los numeros de la presentacion de TimSort siguen dando igual
    assert ordenar("TimSort", list(range(100000)))["comparaciones"] == 99999
    caso1 = list(range(1000, 2000)) + list(range(1000))
    assert ordenar("TimSort", list(caso1))["comparaciones_fusion"] == 45
    assert ordenar("TimSort", list(caso1), galope=False)["comparaciones_fusion"] == 1000
    print("Todo bien")


MENSAJE_SIN_TK = """
Este programa necesita tkinter, la libreria de ventanas de Python.
  Windows y macOS:  instala Python desde https://www.python.org (ya la trae)
  Homebrew:         brew install python-tk
  Ubuntu o Debian:  sudo apt install python3-tk
  Fedora:           sudo dnf install python3-tkinter
"""

MENSAJE_TK_VIEJO = """
Este Python trae Tk {version}, una version antigua que se congela en macOS reciente.
Es el Python que viene con el sistema (/usr/bin/python3). Instala Python desde
https://www.python.org y ejecuta este archivo con ese Python. No hay que instalar
nada mas. Las pruebas sin ventana si funcionan: agrega --prueba al comando.
"""

if tk is None:
    if "--prueba" in sys.argv:
        correr_pruebas()
        sys.exit(0)
    sys.exit(MENSAJE_SIN_TK)


# ---------------------------------------------------------------------------
# Piezas de la interfaz. Todo se dibuja con tkinter, que viene con Python: por
# eso el programa no necesita matplotlib ni ninguna otra instalacion.
# ---------------------------------------------------------------------------
MAX_PASO_A_PASO = 300     # con mas elementos las barras ya no se distinguen
VELOCIDADES = (0.5, 1, 2, 4)
DURACION_PASO = 900       # ms que tarda un paso a velocidad 1x
PAUSA_PASO = 500          # ms para leer entre un paso y otro al reproducir
SECCIONES = (
    ("Algoritmo base", "Mira cómo se mueve cada elemento, paso a paso."),
    ("Representación f(x)", "Mide f(n) y compárala con el mejor y el peor caso teóricos."),
    ("Rendimiento", "El mismo n con distintos tipos de entrada y el efecto del modo galope."),
    ("Demo", "Simula una cantidad de valores y acumula los tiempos."),
    ("Calidad", "Valida correctitud, estabilidad y Big O medido."),
    ("Pseudocódigo", "Lo traduce a Python y lo ejecuta para validar que dé lo mismo que el código."),
    ("Comparación", "Los tres métodos frente a frente."),
)
ICONOS = {
    "primero": (("linea", ((.30, .24), (.30, .76))), ("linea", ((.70, .24), (.42, .50), (.70, .76)))),
    "anterior": (("linea", ((.60, .24), (.34, .50), (.60, .76))),),
    "reproducir": (("poligono", ((.34, .22), (.76, .50), (.34, .78))),),
    "pausa": (("poligono", ((.30, .24), (.44, .24), (.44, .76), (.30, .76))),
              ("poligono", ((.56, .24), (.70, .24), (.70, .76), (.56, .76)))),
    "siguiente": (("linea", ((.40, .24), (.66, .50), (.40, .76))),),
    "ultimo": (("linea", ((.30, .24), (.58, .50), (.30, .76))), ("linea", ((.70, .24), (.70, .76)))),
    "cerrar": (("linea", ((.28, .28), (.72, .72))), ("linea", ((.72, .28), (.28, .72)))),
}


def salida_cubica(t):
    return 1 - (1 - t) ** 3


def entrada_salida(t):
    return t * t * (3 - 2 * t)


def lineal(t):
    return t


def mezclar(color1, color2, t):
    """Color intermedio entre dos colores #rrggbb."""
    canales = []
    for i in (1, 3, 5):
        a, b = int(color1[i:i + 2], 16), int(color2[i:i + 2], 16)
        canales.append(round(a + (b - a) * t))
    return "#%02x%02x%02x" % tuple(canales)


def rectangulo_redondeado(lienzo, x0, y0, x1, y1, radio, **opciones):
    puntos = (x0 + radio, y0, x1 - radio, y0, x1, y0, x1, y0 + radio, x1, y1 - radio, x1, y1,
              x1 - radio, y1, x0 + radio, y1, x0, y1, x0, y1 - radio, x0, y0 + radio, x0, y0)
    return lienzo.create_polygon(puntos, smooth=True, **opciones)


def leer_entero(texto):
    """Acepta tambien el punto de miles (10.000), que es como el programa muestra los numeros."""
    return int(texto.strip().replace(".", ""))


def compacto(x):
    """Numero corto para los ejes: 2.500, 40 mil, 2,5 M."""
    absoluto = abs(x)
    for limite, divisor, sufijo in ((1e9, 1e9, " mM"), (1e6, 1e6, " M"), (1e4, 1e3, " mil")):
        if absoluto >= limite:
            return f"{x / divisor:.4g}".replace(".", ",") + sufijo
    return miles(x) if absoluto >= 1000 else f"{x:.4g}".replace(".", ",")


def marcas_lineales(minimo, maximo, cuantas=5):
    """Marcas redondas (1, 2, 2,5 o 5 por una potencia de 10) que cubren [minimo, maximo]."""
    rango = maximo - minimo
    if rango <= 0:
        rango = abs(maximo) or 1
        maximo = minimo + rango
    base = 10.0 ** math.floor(math.log10(rango / cuantas))
    paso = next(m * base for m in (1, 2, 2.5, 5, 10) if rango / (m * base) <= cuantas)
    primera = math.floor(minimo / paso + 1e-9)
    ultima = math.ceil(maximo / paso - 1e-9)
    return [k * paso for k in range(primera, ultima + 1)]


def limites_log(minimo, maximo):
    """Rango del eje en log10: ajustado a los datos, con un margen para los puntos de los extremos."""
    bajo, alto = math.log10(minimo), math.log10(maximo)
    margen = max(alto - bajo, 0.3) * 0.06
    return bajo - margen, alto + margen


def marcas_log(bajo, alto):
    """Potencias de 10 dentro del rango (en log10); si son pocas agrega el 2 y el 5."""
    exponentes = range(math.floor(bajo), math.ceil(alto) + 1)
    marcas = [10.0 ** k for k in exponentes if bajo <= k <= alto]
    if len(marcas) < 3:
        marcas = [f * 10.0 ** k for k in exponentes for f in (1, 2, 5) if bajo <= k + math.log10(f) <= alto]
    if len(marcas) > 6:
        marcas = marcas[::math.ceil(len(marcas) / 6)]
    return marcas or [10.0 ** ((bajo + alto) / 2)]


def serie(nombre, xs, ys, color, punteada=False, funcion=None, formato=miles):
    """Una curva de Grafica.lineas. 'funcion' da su valor teorico para mostrarlo al pasar el mouse."""
    return {"nombre": nombre, "xs": list(xs), "ys": list(ys), "color": color, "punteada": punteada,
            "funcion": funcion, "formato": formato}


def milisegundos(valor):
    return miles(valor, 1) + " ms"


def colores_de_paso(paso):
    """Color de cada posicion del arreglo segun lo que acaba de pasar."""
    n = len(paso["estado"])
    tipo = paso["tipo"]
    if tipo == "inicio":
        return [AZUL_CLARO] * n
    colores = [GRIS_CLARO] * n
    if tipo == "insercion":
        colores[:paso["hasta"] + 1] = [AZUL] * (paso["hasta"] + 1)
        colores[paso["posicion"]] = DORADO
        return colores
    procesados = sum(paso["pila"])
    colores[:procesados] = [AZUL_PALIDO] * procesados
    inicio, fin = foco_de_paso(paso)
    colores[inicio:fin] = [color_de_paso(paso)] * (fin - inicio)
    return colores


def color_de_paso(paso):
    tipo = paso["tipo"]
    if tipo == "run":
        return DORADO if paso["invertido"] else AZUL
    return {"insercion": DORADO, "fusion": AZUL_OSCURO}.get(tipo, AZUL_CLARO)


def foco_de_paso(paso):
    """Tramo [inicio, fin) del arreglo donde ocurrio el paso."""
    tipo = paso["tipo"]
    if tipo == "insercion":
        return paso["posicion"], paso["hasta"] + 1
    if tipo == "run":
        return paso["inicio"], paso["inicio"] + paso["largo"]
    if tipo == "fusion":
        return paso["inicio"], paso["fin"] + 1
    return 0, len(paso["estado"])


def segmentos_de_paso(paso):
    """Runs de la pila como [(inicio, fin)]: estan seguidos desde la posicion 0."""
    if paso["tipo"] == "insercion":
        return [(0, paso["hasta"] + 1)]
    segmentos, inicio = [], 0
    for largo in paso.get("pila", ()):
        segmentos.append((inicio, inicio + largo))
        inicio += largo
    return segmentos


def describir_paso(paso, es_ultimo):
    """Devuelve (insignia, texto) para mostrar sobre las barras."""
    estado = paso["estado"]
    tipo = paso["tipo"]
    if tipo == "inicio":
        return "INICIO", f"Arreglo original (n = {len(estado)})."
    if tipo == "insercion":
        posicion, hasta = paso["posicion"], paso["hasta"]
        insignia = "INSERCIÓN"
        texto = f"Se insertó el {estado[posicion]} en la posición {posicion}. Zona ordenada: [0-{hasta}]."
    elif tipo == "run":
        inicio, natural, largo = paso["inicio"], paso["natural"], paso["largo"]
        insignia = "RUN INVERTIDO" if paso["invertido"] else "RUN"
        texto = f"Run natural de {natural} elemento(s) en [{inicio}-{inicio + natural - 1}]"
        texto += ", era descendente y se invirtió" if paso["invertido"] else ", ascendente"
        if largo > natural:
            texto += f"; se completó a {largo} con inserción binaria"
        texto += f". Pila de runs: {paso['pila']}"
    else:
        inicio, medio, fin = paso["inicio"], paso["medio"], paso["fin"]
        insignia = "FUSIÓN"
        texto = (f"Se fusionó [{inicio}-{medio}] con [{medio + 1}-{fin}] (merge estable). "
                 f"Pila de runs: {paso['pila']}")
    return insignia, texto + ("  →  arreglo ordenado." if es_ultimo else "")


class Animador:
    """Reloj unico de la interfaz. Las animaciones se basan en el tiempo real:
    en un equipo lento se saltan cuadros pero duran lo mismo. Sin animaciones
    activas no consume nada."""
    INTERVALO = 16

    def __init__(self, raiz):
        self.raiz = raiz
        self.activas = {}
        self.turno = None

    def iniciar(self, clave, duracion, cuadro, suavizado=salida_cubica, al_final=None):
        """Llama cuadro(t) con t de 0 a 1 durante 'duracion' ms. Una animacion
        nueva con la misma clave reemplaza a la anterior."""
        if duracion <= 0:
            self.activas.pop(clave, None)
            cuadro(1.0)
            if al_final:
                al_final()
            return
        self.activas[clave] = (time.perf_counter(), duracion / 1000, cuadro, suavizado, al_final)
        if self.turno is None:
            self.turno = self.raiz.after(self.INTERVALO, self._cuadro)

    def cancelar(self, clave):
        self.activas.pop(clave, None)

    def _cuadro(self):
        self.turno = None
        comienzo = time.perf_counter()
        for clave, entrada in list(self.activas.items()):
            inicio, duracion, cuadro, suavizado, al_final = entrada
            t = min(1.0, (comienzo - inicio) / duracion)
            try:
                cuadro(suavizado(t))
            except tk.TclError:       # el widget ya no existe: se esta cerrando la ventana
                self.activas.pop(clave, None)
                continue
            if t >= 1.0:
                if self.activas.get(clave) is entrada:
                    del self.activas[clave]
                if al_final:
                    al_final()
        if self.activas and self.turno is None:
            gastado = int((time.perf_counter() - comienzo) * 1000)
            self.turno = self.raiz.after(max(1, self.INTERVALO - gastado), self._cuadro)


class Boton(tk.Canvas):
    """Boton dibujado: tk.Button ignora los colores en macOS y ttk cambia segun
    el sistema. Asi se ve igual en todos. Se puede usar con Tab y Enter."""
    ESTILOS = {
        "primario": (AZUL_OSCURO, AZUL, "white", AZUL_OSCURO),
        "secundario": (TARJETA, "#EDF2F9", AZUL_OSCURO, BORDE_FUERTE),
    }

    def __init__(self, padre, app, texto, comando, estilo="secundario", ancho=None, alto=36):
        self.app, self.texto, self.comando = app, texto, comando
        self.colores = self.ESTILOS[estilo]
        self.activo = True
        self.mezcla = 0.0
        self.con_foco = False
        self.letra = app.fuente(13, "bold")
        ancho = ancho or self.letra.measure(texto) + app.px(30)
        super().__init__(padre, bg=padre["bg"], width=ancho, height=app.px(alto), highlightthickness=0,
                         takefocus=1, cursor="hand2")
        self.bind("<Enter>", lambda _: self._sobre(True))
        self.bind("<Leave>", lambda _: self._sobre(False))
        self.bind("<ButtonRelease-1>", self._soltar)
        self.bind("<Return>", lambda _: self._pulsar())
        self.bind("<space>", lambda _: self._pulsar())
        self.bind("<FocusIn>", lambda _: self._foco(True))
        self.bind("<FocusOut>", lambda _: self._foco(False))
        self._dibujar()

    def _sobre(self, dentro):
        if not self.activo:
            return
        desde, hasta = self.mezcla, 1.0 if dentro else 0.0

        def cuadro(t):
            self.mezcla = desde + (hasta - desde) * t
            self._dibujar()
        self.app.animador.iniciar(self, 130, cuadro)

    def _foco(self, con_foco):
        self.con_foco = con_foco
        self._dibujar()

    def _soltar(self, evento):
        if 0 <= evento.x < self.winfo_width() and 0 <= evento.y < self.winfo_height():
            self._pulsar()

    def _pulsar(self):
        if self.activo:
            self.comando()

    def habilitar(self, activo):
        self.activo = activo
        self.mezcla = 0.0
        self.configure(cursor="hand2" if activo else "arrow")
        self._dibujar()

    def cambiar_texto(self, texto):
        self.texto = texto
        self.configure(width=self.letra.measure(texto) + self.app.px(30))
        self._dibujar()

    def _colores_actuales(self):
        fondo, sobre, letra, borde = self.colores
        if not self.activo:
            return "#E8ECF3", "#98A4B6", "#E8ECF3"
        return mezclar(fondo, sobre, self.mezcla), letra, AZUL if self.con_foco else borde

    def _dibujar(self):
        self.delete("all")
        fondo, letra, borde = self._colores_actuales()
        ancho, alto = int(self["width"]), int(self["height"])
        rectangulo_redondeado(self, 1, 1, ancho - 2, alto - 2, self.app.px(7), fill=fondo, outline=borde)
        self.create_text(ancho / 2, alto / 2, text=self.texto, fill=letra, font=self.letra)


class BotonIcono(Boton):
    """Los iconos son figuras y no caracteres: un simbolo como el de reproducir
    se ve distinto (o sale como emoji) segun el sistema y la fuente."""

    def __init__(self, padre, app, icono, comando, estilo="secundario", lado=36):
        self.icono = icono
        super().__init__(padre, app, "", comando, estilo, ancho=app.px(lado), alto=lado)

    def cambiar_icono(self, icono):
        self.icono = icono
        self._dibujar()

    def _dibujar(self):
        self.delete("all")
        fondo, letra, borde = self._colores_actuales()
        lado = int(self["width"])
        rectangulo_redondeado(self, 1, 1, lado - 2, lado - 2, self.app.px(7), fill=fondo, outline=borde)
        for tipo, puntos in ICONOS[self.icono]:
            coordenadas = [valor * lado for punto in puntos for valor in punto]
            if tipo == "linea":
                self.create_line(coordenadas, fill=letra, width=self.app.px(2.2), capstyle="round", joinstyle="round")
            else:
                self.create_polygon(coordenadas, fill=letra, outline=letra)


class Segmentos(tk.Canvas):
    """Selector de opciones con una pastilla que se desliza hasta la elegida."""

    def __init__(self, padre, app, opciones, inicial, al_cambiar):
        self.app, self.opciones, self.al_cambiar = app, opciones, al_cambiar
        self.actual = inicial
        self.letra = app.fuente(12, "bold")
        self.ancho_opcion = max(self.letra.measure(o) for o in opciones) + app.px(16)
        self.x_pastilla = float(inicial * self.ancho_opcion)
        super().__init__(padre, bg=padre["bg"], width=self.ancho_opcion * len(opciones), height=app.px(32),
                         highlightthickness=0, cursor="hand2")
        self.bind("<Button-1>", self._clic)
        self._dibujar()

    def _clic(self, evento):
        indice = min(len(self.opciones) - 1, max(0, evento.x // self.ancho_opcion))
        if indice == self.actual:
            return
        self.actual = indice
        desde, hasta = self.x_pastilla, indice * self.ancho_opcion

        def cuadro(t):
            self.x_pastilla = desde + (hasta - desde) * t
            self._dibujar()
        self.app.animador.iniciar(self, 200, cuadro)
        self.al_cambiar(indice)

    def _dibujar(self):
        self.delete("all")
        ancho, alto, px = int(self["width"]), int(self["height"]), self.app.px
        rectangulo_redondeado(self, 0, 0, ancho - 1, alto - 1, px(8), fill="#E9EEF6", outline="")
        rectangulo_redondeado(self, self.x_pastilla + px(3), px(3), self.x_pastilla + self.ancho_opcion - px(3),
                              alto - px(3), px(6), fill=TARJETA, outline=BORDE_FUERTE)
        for i, opcion in enumerate(self.opciones):
            color = AZUL_OSCURO if i == self.actual else TEXTO_SUAVE
            self.create_text((i + 0.5) * self.ancho_opcion, alto / 2, text=opcion, fill=color, font=self.letra)


class Menu(tk.Canvas):
    """Lista de la columna izquierda; la marca de la fila elegida se desliza."""

    def __init__(self, padre, app, filas, al_elegir, alto_fila=36):
        self.app, self.filas, self.al_elegir = app, filas, al_elegir
        self.alto_fila = app.px(alto_fila)
        self.actual = 0
        self.sobre = None
        self.y_marca = 0.0
        super().__init__(padre, bg=padre["bg"], height=self.alto_fila * len(filas), width=1,
                         highlightthickness=0, cursor="hand2")
        self.bind("<Configure>", lambda _: self._dibujar())
        self.bind("<Motion>", self._mover)
        self.bind("<Leave>", self._salir)
        self.bind("<Button-1>", self._clic)

    def _fila_de(self, y):
        return min(len(self.filas) - 1, max(0, y // self.alto_fila))

    def _mover(self, evento):
        fila = self._fila_de(evento.y)
        if fila != self.sobre:
            self.sobre = fila
            self._dibujar()

    def _salir(self, _evento):
        self.sobre = None
        self._dibujar()

    def _clic(self, evento):
        fila = self._fila_de(evento.y)
        if fila != self.actual:
            self.al_elegir(fila)

    def elegir(self, fila):
        self.actual = fila
        desde, hasta = self.y_marca, fila * self.alto_fila

        def cuadro(t):
            self.y_marca = desde + (hasta - desde) * t
            self._dibujar()
        self.app.animador.iniciar(self, 240, cuadro)

    def _dibujar(self):
        self.delete("all")
        ancho, alto, px = self.winfo_width(), self.alto_fila, self.app.px
        if self.sobre is not None and self.sobre != self.actual:
            y = self.sobre * alto
            rectangulo_redondeado(self, px(10), y + px(2), ancho - px(10), y + alto - px(2), px(7),
                                  fill=COLUMNA_SOBRE, outline="")
        y = self.y_marca
        rectangulo_redondeado(self, px(10), y + px(2), ancho - px(10), y + alto - px(2), px(7),
                              fill=COLUMNA_ACTIVA, outline="")
        self.create_rectangle(px(10), y + px(9), px(13), y + alto - px(9), fill=DORADO, outline="")
        for i, fila in enumerate(self.filas):
            medio = (i + 0.5) * alto
            elegida = i == self.actual
            if "color" in fila:
                r = px(5)
                self.create_oval(px(23) - r, medio - r, px(23) + r, medio + r, fill=fila["color"], outline="white")
            else:
                self.create_text(px(23), medio, text=fila["numero"], font=self.app.fuente(12, "bold"),
                                 fill=DORADO if elegida else COLUMNA_TEXTO)
            self.create_text(px(38), medio, text=fila["texto"], anchor="w", font=self.app.fuente(13, "bold" if elegida else "normal"),
                             fill="white" if elegida else COLUMNA_TEXTO)
            if "detalle" in fila:
                self.create_text(ancho - px(18), medio, text=fila["detalle"], anchor="e", font=self.app.fuente(11),
                                 fill=COLUMNA_TEXTO)


class LineaTiempo(tk.Canvas):
    """Recorrido del paso a paso: se puede hacer clic o arrastrar."""

    def __init__(self, padre, app, al_cambiar):
        self.app, self.al_cambiar = app, al_cambiar
        self.colores = []
        self.actual = 0
        self.posicion = 0.0
        super().__init__(padre, bg=padre["bg"], height=app.px(32), width=app.px(120), highlightthickness=0, cursor="hand2")
        self.bind("<Configure>", lambda _: self._dibujar())
        self.bind("<Button-1>", self._elegir)
        self.bind("<B1-Motion>", self._elegir)

    def cargar(self, colores):
        self.app.animador.cancelar(self)
        self.colores = colores
        self.actual = 0
        self.posicion = 0.0
        self._dibujar()

    def marcar(self, indice):
        desde = self.posicion
        self.actual = indice

        def cuadro(t):
            self.posicion = desde + (indice - desde) * t
            self._dibujar()
        self.app.animador.iniciar(self, 240, cuadro)

    def _x(self, indice):
        margen = self.app.px(11)
        return margen + (self.winfo_width() - 2 * margen) * indice / max(1, len(self.colores) - 1)

    def _elegir(self, evento):
        if len(self.colores) < 2:
            return
        margen = self.app.px(11)
        fraccion = (evento.x - margen) / max(1, self.winfo_width() - 2 * margen)
        indice = round(min(1.0, max(0.0, fraccion)) * (len(self.colores) - 1))
        if indice != self.actual:
            self.al_cambiar(indice)

    def _dibujar(self):
        self.delete("all")
        if self.winfo_width() < 30 or not self.colores:
            return
        px, y = self.app.px, self.winfo_height() / 2
        x = self._x(self.posicion)
        self.create_line(self._x(0), y, self._x(len(self.colores) - 1), y, fill=BORDE, width=px(4), capstyle="round")
        self.create_line(self._x(0), y, x, y, fill=AZUL_OSCURO, width=px(4), capstyle="round")
        if self.winfo_width() / len(self.colores) >= px(7):
            r = px(2.5)
            for i, color in enumerate(self.colores):
                xi = self._x(i)
                self.create_oval(xi - r, y - r, xi + r, y + r, fill=color, outline=TARJETA)
        r = px(8)
        self.create_oval(x - r, y - r, x + r, y + r, fill=TARJETA, outline=AZUL_OSCURO, width=px(2))


class BarraProgreso(tk.Canvas):
    """Linea delgada bajo el titulo con el avance de la medicion. No se anima a
    proposito: mientras se mide, la ventana debe gastar lo minimo."""

    def __init__(self, padre, app):
        super().__init__(padre, bg=padre["bg"], height=app.px(3), width=1, highlightthickness=0)
        self.valor = None
        self.bind("<Configure>", lambda _: self.poner(self.valor))

    def poner(self, valor):
        self.valor = valor
        self.delete("all")
        if valor is not None:
            self.create_rectangle(0, 0, self.winfo_width(), 10, fill=BORDE, outline="")
            self.create_rectangle(0, 0, self.winfo_width() * valor, 10, fill=DORADO, outline="")


class Parrafo(tk.Label):
    """Etiqueta cuyo texto se ajusta solo al ancho disponible."""

    def __init__(self, padre, **opciones):
        opciones.setdefault("justify", "left")
        opciones.setdefault("anchor", "nw")
        super().__init__(padre, **opciones)
        self.bind("<Configure>", lambda e: self.configure(wraplength=max(60, e.width - 4)))


class Campo(tk.Frame):
    """Entrada de texto con titulo; el borde indica el foco y los errores."""

    def __init__(self, padre, app, titulo, valor="", ancho=8, al_enter=None):
        super().__init__(padre, bg=padre["bg"])
        self.app = app
        tk.Label(self, text=titulo, bg=padre["bg"], fg=TEXTO_SUAVE, font=app.fuente(12), anchor="w").pack(
            fill="x", pady=(0, app.px(3)))
        self.borde = tk.Frame(self, bg=BORDE_FUERTE)
        self.borde.pack(fill="x")
        self.interior = tk.Frame(self.borde, bg="white")
        self.interior.pack(fill="both", expand=True, padx=1, pady=1)
        self.entrada = tk.Entry(self.interior, width=ancho, relief="flat", bd=0, highlightthickness=0, bg="white",
                                fg=TINTA, insertbackground=TINTA, selectbackground=AZUL_PALIDO, selectforeground=TINTA,
                                disabledbackground="#EEF1F6", disabledforeground="#98A4B6", font=app.fuente(13))
        self.entrada.pack(fill="x", padx=app.px(8), pady=app.px(6))
        self.entrada.insert(0, valor)
        self.entrada.bind("<FocusIn>", lambda _: self.borde.config(bg=AZUL))
        self.entrada.bind("<FocusOut>", lambda _: self.borde.config(bg=BORDE_FUERTE))
        if al_enter:
            self.entrada.bind("<Return>", lambda _: al_enter())

    def get(self):
        return self.entrada.get()

    def set(self, valor):
        self.entrada.delete(0, "end")
        self.entrada.insert(0, valor)

    def habilitar(self, activo):
        self.entrada.config(state="normal" if activo else "disabled")
        self.interior.config(bg="white" if activo else "#EEF1F6")

    def marcar_error(self):
        """El borde se pone rojo y vuelve despacio a su color."""
        self.entrada.focus_set()
        self.entrada.selection_range(0, "end")
        self.app.animador.iniciar(self, 1600, lambda t: self.borde.config(bg=mezclar(ROJO, AZUL, t)), lineal, self._restaurar_borde)

    def _restaurar_borde(self):
        self.borde.config(bg=AZUL if self.focus_get() is self.entrada else BORDE_FUERTE)


class Selector(tk.Frame):
    def __init__(self, padre, app, titulo, opciones, valor, ancho=18):
        super().__init__(padre, bg=padre["bg"])
        tk.Label(self, text=titulo, bg=padre["bg"], fg=TEXTO_SUAVE, font=app.fuente(12), anchor="w").pack(
            fill="x", pady=(0, app.px(3)))
        self.combo = ttk.Combobox(self, values=opciones, state="readonly", width=ancho, font=app.fuente(13))
        self.combo.set(valor)
        self.combo.pack(fill="x", ipady=app.px(5))
        self.combo.bind("<<ComboboxSelected>>", lambda _: (self.combo.selection_clear(), app.focus_set()))

    def get(self):
        return self.combo.get()


class FilaFluida(tk.Frame):
    """Fila de controles: lo que no cabe baja a la linea siguiente, asi sirve
    igual en un portatil pequeno que en un monitor grande."""

    def __init__(self, padre, app):
        super().__init__(padre, bg=padre["bg"], height=app.px(58))
        self.hueco = app.px(12)
        self.hijos = []
        self.ancho_anterior = None
        self.bind("<Configure>", self._acomodar)

    def agregar(self, hijo, expandir=False):
        self.hijos.append((hijo, expandir))
        return hijo

    def _acomodar(self, _evento=None):
        ancho = self.winfo_width()
        if ancho <= 1 or ancho == self.ancho_anterior:
            return
        self.ancho_anterior = ancho
        filas, fila, usado = [], [], 0
        for hijo, expandir in self.hijos:
            pedido = hijo.winfo_reqwidth()
            if fila and usado + pedido > ancho:
                filas.append(fila)
                fila, usado = [], 0
            fila.append((hijo, expandir, pedido))
            usado += pedido + self.hueco
        filas.append(fila)
        y = 0
        for fila in filas:
            alto = max(hijo.winfo_reqheight() for hijo, _, _ in fila)
            sobra = ancho - sum(pedido for _, _, pedido in fila) - self.hueco * (len(fila) - 1)
            expandibles = sum(1 for _, expandir, _ in fila if expandir)
            x = 0
            for hijo, expandir, pedido in fila:
                if expandir:
                    pedido += sobra // expandibles
                hijo.place(x=x, y=y + alto - hijo.winfo_reqheight(), width=pedido, height=hijo.winfo_reqheight())
                x += pedido + self.hueco
            y += alto + self.hueco
        self.configure(height=y - self.hueco)


class Seccion(tk.Frame):
    """Contenido de una seccion. Si la ventana alcanza, las graficas crecen
    para llenarla; si no alcanza, hay scroll en lugar de controles cortados."""

    def __init__(self, padre, app):
        super().__init__(padre, bg=FONDO)
        self.lienzo = tk.Canvas(self, bg=FONDO, highlightthickness=0, yscrollincrement=app.px(24))
        self.lienzo.pack(fill="both", expand=True)
        self.barra = ttk.Scrollbar(self, orient="vertical", command=self.lienzo.yview)
        self.ancho_barra = app.px(12)
        self.lienzo.configure(yscrollcommand=self.barra.set)
        self.cuerpo = tk.Frame(self.lienzo, bg=FONDO)
        self.ventana = self.lienzo.create_window(0, 0, anchor="nw", window=self.cuerpo)
        self.lienzo.bind("<Configure>", self._ajustar)
        self.cuerpo.bind("<Configure>", self._ajustar)

    def _ajustar(self, _evento=None):
        ancho, alto = self.lienzo.winfo_width(), self.lienzo.winfo_height()
        necesario = self.cuerpo.winfo_reqheight()
        total = max(alto, necesario)
        self.lienzo.itemconfigure(self.ventana, width=ancho, height=total)
        self.lienzo.configure(scrollregion=(0, 0, ancho, total))
        if necesario > alto:
            self.barra.place(relx=1, rely=0, relheight=1, anchor="ne", width=self.ancho_barra)
        else:
            self.barra.place_forget()
            self.lienzo.yview_moveto(0)

    def desplazar(self, unidades):
        if self.cuerpo.winfo_reqheight() > self.lienzo.winfo_height():
            self.lienzo.yview_scroll(unidades, "units")


class Indicador(tk.Frame):
    """Resultado grande de una validacion; el numero sube contando."""

    def __init__(self, padre, app, titulo):
        super().__init__(padre, bg=TARJETA, highlightbackground=BORDE, highlightcolor=BORDE, highlightthickness=1)
        self.app = app
        self.numero = tk.Label(self, text="-", bg=TARJETA, fg=BORDE_FUERTE, font=app.fuente(25, "bold"), anchor="w")
        self.numero.pack(fill="x", padx=app.px(14), pady=(app.px(8), 0))
        tk.Label(self, text=titulo, bg=TARJETA, fg=TEXTO_SUAVE, font=app.fuente(12), anchor="w").pack(
            fill="x", padx=app.px(14), pady=(0, app.px(9)))

    def poner(self, valor, total):
        self.numero.config(fg=VERDE if valor == total else ROJO)
        self.app.animador.iniciar(self, 800, lambda t: self.numero.config(text=f"{round(valor * t)}/{total}"))

    def limpiar(self):
        self.app.animador.cancelar(self)
        self.numero.config(text="-", fg=BORDE_FUERTE)


class Grafica(tk.Canvas):
    """Grafica dibujada sobre un Canvas: hace el trabajo que antes hacia
    matplotlib. Dibuja lineas y barras en escala lineal o logaritmica, se adapta
    al tamano, aparece animada y muestra los valores al pasar el mouse."""

    def __init__(self, padre, app, vacio, alto=230):
        super().__init__(padre, bg=TARJETA, highlightthickness=0, width=app.px(220), height=app.px(alto))
        self.app, self.vacio = app, vacio
        self.datos = None
        self.avance = 1.0
        self.puntero = None
        self.columnas, self.bandas = [], []
        self.plano = (0, 0, 0, 0)
        self.bind("<Configure>", lambda _: self._dibujar())
        self.bind("<Motion>", self._mover)
        self.bind("<Leave>", self._salir)

    def vaciar(self, mensaje=None):
        self.app.animador.cancelar(self)
        self.datos = None
        self.vacio = mensaje or self.vacio
        self._dibujar()

    def lineas(self, titulo, series, eje_x="", eje_y="", log=False, rango_y=None, referencias=()):
        leyenda = [(s["nombre"], s["color"], s["punteada"]) for s in series]
        self._mostrar({"tipo": "lineas", "titulo": titulo, "series": series, "eje_x": eje_x, "eje_y": eje_y,
                       "log": log, "rango_y": rango_y, "referencias": referencias, "leyenda": leyenda})

    def barras(self, titulo, etiquetas, series, eje_x="", eje_y="", referencias=()):
        """Cada serie es un dict con 'valores', 'colores' (uno por barra), y
        opcionalmente 'nombre' y 'textos' (lo que se escribe sobre cada barra)."""
        leyenda = [(s["nombre"], s["colores"][0], False) for s in series if s.get("nombre")]
        leyenda += [(nombre, color, True) for _, color, nombre in referencias]
        self._mostrar({"tipo": "barras", "titulo": titulo, "etiquetas": etiquetas, "series": series, "eje_x": eje_x,
                       "eje_y": eje_y, "referencias": referencias, "leyenda": leyenda})

    def _mostrar(self, datos):
        self.datos = datos
        self.avance = 0.0
        self.app.animador.iniciar(self, 750, self._fotograma, lineal)

    def _fotograma(self, t):
        self.avance = t
        self._dibujar()

    def _mover(self, evento):
        self.puntero = (evento.x, evento.y)
        self._pintar_puntero()

    def _salir(self, _evento):
        self.puntero = None
        self.delete("puntero")

    def _dibujar(self):
        self.delete("all")
        ancho, alto = self.winfo_width(), self.winfo_height()
        if ancho < 40 or alto < 40:
            return
        if self.datos is None:
            self.create_text(ancho / 2, alto / 2, text=self.vacio, fill=TEXTO_SUAVE, font=self.app.fuente(13),
                             width=ancho - self.app.px(30), justify="center")
            return
        arriba = self._encabezado(ancho)
        if self.datos["tipo"] == "lineas":
            self._dibujar_lineas(ancho, alto, arriba)
        else:
            self._dibujar_barras(ancho, alto, arriba)
        self._pintar_puntero()

    def _encabezado(self, ancho):
        """Titulo y leyenda. Devuelve la 'y' donde puede empezar la grafica."""
        px, letra = self.app.px, self.app.fuente(12)
        linea = letra.metrics("linespace") + px(3)
        titulo = self.create_text(px(8), px(6), text=self.datos["titulo"], anchor="nw", fill=TINTA,
                                  font=self.app.fuente(13, "bold"), width=ancho - px(16))
        y = self.bbox(titulo)[3] + px(4)
        x = px(8)
        for nombre, color, punteada in self.datos["leyenda"]:
            pedido = px(22) + letra.measure(nombre) + px(10)
            if x > px(8) and x + pedido > ancho - px(8):
                x = px(8)
                y += linea
            medio = y + linea / 2
            self.create_line(x, medio, x + px(16), medio, fill=color, width=px(2.5), dash=(4, 3) if punteada else None)
            self.create_text(x + px(21), medio, text=nombre, anchor="w", font=letra, fill=TEXTO_SUAVE)
            x += pedido
        return y + (linea if self.datos["leyenda"] else 0)

    def _ejes(self, marcas_y, ancho, alto, arriba, pie):
        """Reserva el espacio de los ejes y devuelve (izq, der, sup, inf)."""
        px, letra = self.app.px, self.app.fuente(11)
        sup = arriba + px(6)
        if self.datos["eje_y"]:
            self.create_text(px(8), arriba + px(2), text=self.datos["eje_y"], anchor="nw", font=letra, fill=TEXTO_SUAVE)
            sup += letra.metrics("linespace") + px(6)
        if self.datos["eje_x"]:
            pie += letra.metrics("linespace")
            self.create_text(ancho / 2, alto - px(3), text=self.datos["eje_x"], anchor="s", font=letra, fill=TEXTO_SUAVE)
        izq = px(8) + max(letra.measure(compacto(m)) for m in marcas_y) + px(8)
        self.plano = izq, ancho - px(28), sup, alto - pie      # a la derecha cabe media marca del eje x
        return self.plano

    def _lineas_y(self, marcas_y, a_y):
        izq, der, _, _ = self.plano
        letra = self.app.fuente(11)
        for marca in marcas_y:
            y = a_y(marca)
            self.create_line(izq, y, der, y, fill=BORDE)
            self.create_text(izq - self.app.px(6), y, text=compacto(marca), anchor="e", font=letra, fill=TEXTO_SUAVE)

    def _dibujar_lineas(self, ancho, alto, arriba):
        d, px = self.datos, self.app.px
        series, log = d["series"], d["log"]
        xs = [x for s in series for x in s["xs"] if x > 0 or not log]
        ys = [y for s in series for y in s["ys"] if y > 0 or not log]
        valores_ref = [valor for valor, _, _ in d["referencias"]]
        if log:
            lo_y, hi_y = limites_log(min(ys), max(ys))
            marcas_y = marcas_log(lo_y, hi_y)
        else:
            if d["rango_y"]:
                marcas_y = marcas_lineales(min(d["rango_y"][0], *ys), max(d["rango_y"][1], *ys), 4)
            else:
                marcas_y = marcas_lineales(0, max(ys + valores_ref))
            lo_y, hi_y = marcas_y[0], marcas_y[-1]
        izq, der, sup, inf = self._ejes(marcas_y, ancho, alto, arriba, px(20))
        if log:
            lo_x, hi_x = limites_log(min(xs), max(xs))
            marcas_x = marcas_log(lo_x, hi_x)
        else:
            marcas_x = marcas_lineales(0, max(xs), max(2, int((der - izq) / px(80))))
            lo_x, hi_x = marcas_x[0], marcas_x[-1]
        t = math.log10 if log else float

        def a_x(valor):
            return izq + (t(valor) - lo_x) / (hi_x - lo_x) * (der - izq)

        def a_y(valor):
            return inf - (t(valor) - lo_y) / (hi_y - lo_y) * (inf - sup)

        self._lineas_y(marcas_y, a_y)
        letra = self.app.fuente(11)
        for marca in marcas_x:
            self.create_text(a_x(marca), inf + px(5), text=compacto(marca), anchor="n", font=letra, fill=TEXTO_SUAVE)
        for valor, color, _ in d["referencias"]:
            self.create_line(izq, a_y(valor), der, a_y(valor), fill=color, dash=(5, 3))

        limite = izq + (der - izq) * salida_cubica(self.avance)
        for s in series:
            puntos = [(a_x(x), a_y(y)) for x, y in zip(s["xs"], s["ys"]) if not log or (x > 0 and y > 0)]
            visibles = self._recortar(puntos, limite)
            if len(visibles) > 1:
                self.create_line([v for punto in visibles for v in punto], fill=s["color"], width=px(2.5),
                                 dash=(6, 4) if s["punteada"] else None, capstyle="round", joinstyle="round")
            if not s["punteada"]:
                r = px(3.5)
                for x, y in puntos:
                    if x <= limite:
                        self.create_oval(x - r, y - r, x + r, y + r, fill=TARJETA, outline=s["color"], width=px(2))

        columnas = {}
        for s in series:
            if not s["punteada"]:
                for x, y in zip(s["xs"], s["ys"]):
                    columnas.setdefault(x, []).append((s, y))
        teoricas = [s for s in series if s["punteada"] and s["funcion"]]
        self.columnas = []
        for x in sorted(columnas):
            filas = [(s["color"], s["nombre"], s["formato"](y)) for s, y in columnas[x]]
            filas += [(s["color"], s["nombre"], s["formato"](s["funcion"](x))) for s in teoricas]
            marcadores = [(a_y(y), s["color"]) for s, y in columnas[x] if y > 0 or not log]
            self.columnas.append((a_x(x), miles(x), filas, marcadores))

    @staticmethod
    def _recortar(puntos, limite):
        """Parte de la curva a la izquierda de 'limite': asi la linea se va trazando."""
        visibles = []
        for punto in puntos:
            if punto[0] <= limite:
                visibles.append(punto)
                continue
            if visibles:
                (x0, y0), (x1, y1) = visibles[-1], punto
                visibles.append((limite, y0 + (y1 - y0) * (limite - x0) / ((x1 - x0) or 1)))
            break
        return visibles

    def _dibujar_barras(self, ancho, alto, arriba):
        d, px = self.datos, self.app.px
        series, etiquetas = d["series"], d["etiquetas"]
        letra = self.app.fuente(11)
        renglones = max(etiqueta.count("\n") + 1 for etiqueta in etiquetas)
        pie = px(8) + renglones * letra.metrics("linespace")
        maximo = max([v for s in series for v in s["valores"]] + [valor for valor, _, _ in d["referencias"]])
        marcas_y = marcas_lineales(0, maximo * 1.1)
        izq, der, sup, inf = self._ejes(marcas_y, ancho, alto, arriba, pie)
        tope = marcas_y[-1] or 1

        def a_y(valor):
            return inf - valor / tope * (inf - sup)

        self._lineas_y(marcas_y, a_y)
        banda = (der - izq) / len(etiquetas)
        ancho_barra = min(banda * 0.72 / len(series), px(70))
        self.bandas = []
        for i, etiqueta in enumerate(etiquetas):
            centro = izq + (i + 0.5) * banda
            self.create_text(centro, inf + px(5), text=etiqueta, anchor="n", justify="center", font=letra, fill=TEXTO_SUAVE)
            subida = salida_cubica(min(1.0, max(0.0, self.avance * 1.5 - i * 0.1)))
            filas = []
            for k, s in enumerate(series):
                valor = s["valores"][i]
                x0 = centro + (k - len(series) / 2) * ancho_barra
                y = a_y(valor * subida)
                self.create_rectangle(x0 + 1, y, x0 + ancho_barra - 1, inf, fill=s["colores"][i], outline="")
                texto = s["textos"][i] if s.get("textos") else miles(valor, 1)
                filas.append((s["colores"][i], s.get("nombre") or "Valor", texto))
                if s.get("textos") and letra.measure(texto) < banda:
                    self.create_text(x0 + ancho_barra / 2, y - px(3), text=texto, anchor="s", font=letra, fill=TINTA)
            titulo = etiqueta.replace("\n", " ")
            self.bandas.append((izq + i * banda, izq + (i + 1) * banda, titulo, filas))
        self.create_line(izq, inf, der, inf, fill=BORDE_FUERTE)
        for valor, color, _ in d["referencias"]:
            self.create_line(izq, a_y(valor), der, a_y(valor), fill=color, dash=(5, 3), width=px(1.5))

    def _pintar_puntero(self):
        self.delete("puntero")
        if self.puntero is None or self.datos is None or self.avance < 1.0:
            return
        x, y = self.puntero
        izq, der, sup, inf = self.plano
        if not (izq - 10 <= x <= der + 10 and sup <= y <= inf):
            return
        if self.datos["tipo"] == "lineas":
            if self.columnas:
                columna, titulo, filas, marcadores = min(self.columnas, key=lambda c: abs(c[0] - x))
                self.create_line(columna, sup, columna, inf, fill=BORDE_FUERTE, tags="puntero")
                r = self.app.px(5)
                for yp, color in marcadores:
                    self.create_oval(columna - r, yp - r, columna + r, yp + r, fill=color, outline=TARJETA, tags="puntero")
                self._globo(columna, y, f"n = {titulo}", filas)
        else:
            for x0, x1, titulo, filas in self.bandas:
                if x0 <= x <= x1:
                    self._globo(x, y, titulo, filas)
                    break

    def _globo(self, x, y, titulo, filas):
        """Recuadro con los valores bajo el puntero; nunca se sale de la grafica."""
        px = self.app.px
        negrita, letra = self.app.fuente(12, "bold"), self.app.fuente(12)
        linea = letra.metrics("linespace") + px(3)
        ancho_texto = max([negrita.measure(titulo)] + [px(14) + letra.measure(f"{nombre}: {valor}") for _, nombre, valor in filas])
        ancho, alto = ancho_texto + px(20), linea * (len(filas) + 1) + px(12)
        x0 = x + px(14) if x + px(14) + ancho < self.winfo_width() - px(4) else x - px(14) - ancho
        x0 = max(px(4), x0)
        y0 = max(px(4), min(y - alto / 2, self.winfo_height() - alto - px(4)))
        rectangulo_redondeado(self, x0, y0, x0 + ancho, y0 + alto, px(6), fill=TINTA, outline="", tags="puntero")
        self.create_text(x0 + px(10), y0 + px(6), text=titulo, anchor="nw", font=negrita, fill="white", tags="puntero")
        for i, (color, nombre, valor) in enumerate(filas, 1):
            yf = y0 + px(6) + linea * i + linea / 2
            r = px(4)
            self.create_oval(x0 + px(10), yf - r, x0 + px(10) + 2 * r, yf + r, fill=color, outline="", tags="puntero")
            self.create_text(x0 + px(24), yf, text=f"{nombre}: {valor}", anchor="w", font=letra, fill="white", tags="puntero")


class LienzoBarras(tk.Canvas):
    """El arreglo como barras con identidad propia: al cambiar de paso cada una
    se desliza hasta su nueva posicion en lugar de redibujarse. Los metodos son
    estables, asi que el k-esimo valor repetido siempre es el mismo elemento."""
    MAX_ANIMADAS = 160        # con mas barras se pasa directo al resultado

    def __init__(self, padre, app):
        super().__init__(padre, bg=TARJETA, highlightthickness=0, width=app.px(300), height=app.px(190))
        self.app = app
        self.barras = []
        self.titulo_pista = ""
        self.segmentos_desde, self.segmentos = {}, []
        self.foco_desde = self.foco_actual = self.foco_hacia = (0.0, 0.0)
        self.color_banda, self.color_foco = TARJETA, AZUL_CLARO
        self.ola = 0.0
        self.progreso_pista = 1.0
        self.banda = None
        self.minimo, self.maximo = 0, 1
        self.bind("<Configure>", lambda _: self._repintar())

    def cargar(self, paso, titulo_pista):
        """Crea una barra por elemento. Las barras suben una tras otra."""
        self.app.animador.cancelar(self)
        self.delete("all")
        estado = paso["estado"]
        colores = colores_de_paso(paso)
        self.titulo_pista = titulo_pista
        self.minimo, self.maximo = min(0, min(estado)), max(0, max(estado))
        self.banda = self.create_rectangle(0, 0, 0, 0, fill=TARJETA, outline="")
        self.segmentos_desde, self.segmentos = {}, []
        self.foco_desde = self.foco_actual = self.foco_hacia = (0.0, 0.0)
        self.color_banda = TARJETA
        self.barras = []
        vistos = {}
        con_texto = len(estado) <= 40
        for i, valor in enumerate(estado):
            k = vistos.get(valor, 0)
            vistos[valor] = k + 1
            self.barras.append({
                "clave": (valor, k), "valor": valor, "pos": float(i), "desde": float(i), "hasta": float(i),
                "color": colores[i], "color_desde": colores[i], "color_hasta": colores[i], "salto": 0.0, "impulso": 0.0,
                "retardo": 0.0, "factor": 0.0, "pintado": colores[i],
                "rect": self.create_rectangle(0, 0, 0, 0, fill=colores[i], outline=""),
                "texto": self.create_text(0, 0, text=str(valor), font=self.app.fuente(12, "bold"), fill=TINTA) if con_texto else None,
            })
        self._repintar()
        self.app.animador.iniciar(self, 650, self._crecer, lineal)

    def _crecer(self, t):
        n = len(self.barras)
        for i, barra in enumerate(self.barras):
            barra["factor"] = salida_cubica(min(1.0, max(0.0, t * 1.6 - 0.6 * i / n)))
            self._colocar(barra)

    def ir_a(self, paso, duracion, ola=0.0, al_final=None):
        """Lleva cada barra a su posicion en 'paso'. 'ola' (de 0 a 1) reparte el
        arranque de izquierda a derecha, como avanza una fusion real."""
        self.app.animador.cancelar(self)
        colores = colores_de_paso(paso)
        destino, vistos = {}, {}
        for i, valor in enumerate(paso["estado"]):
            k = vistos.get(valor, 0)
            vistos[valor] = k + 1
            destino[(valor, k)] = i
        inicio, fin = foco_de_paso(paso)
        alcance = max(1, fin - inicio - 1)
        self.ola = ola
        for barra in self.barras:
            hasta = destino[barra["clave"]]
            distancia = abs(hasta - barra["pos"])
            se_mueve = distancia > 0.01
            barra["factor"] = 1.0
            barra["desde"], barra["hasta"] = barra["pos"], hasta
            barra["color_desde"], barra["color_hasta"] = barra["color"], colores[hasta]
            barra["retardo"] = ola * min(1.0, max(0.0, (hasta - inicio) / alcance)) if se_mueve else 0.0
            barra["impulso"] = min(self.app.px(26), self.app.px(5) + distancia * self.paso_x * 0.14) if se_mueve else 0.0
            if se_mueve:
                self.tag_raise(barra["rect"])
                if barra["texto"]:
                    self.tag_raise(barra["texto"])
        self.foco_desde, self.foco_hacia = self.foco_actual, (float(inicio), float(fin))
        color = color_de_paso(paso)
        self.color_banda = TARJETA if paso["tipo"] == "inicio" else mezclar(color, TARJETA, 0.86)
        self.color_foco = color
        self.itemconfigure(self.banda, fill=self.color_banda)
        self.segmentos_desde = dict(self.segmentos)
        self.segmentos = segmentos_de_paso(paso)
        if len(self.barras) > self.MAX_ANIMADAS:
            duracion = 0
        self.app.animador.iniciar(self, duracion, self._cuadro, lineal, al_final)

    def _cuadro(self, t):
        ola = self.ola
        for barra in self.barras:
            local = min(1.0, max(0.0, (t - barra["retardo"]) / (1 - ola)))
            suave = entrada_salida(local)
            barra["pos"] = barra["desde"] + (barra["hasta"] - barra["desde"]) * suave
            barra["salto"] = math.sin(math.pi * local) * barra["impulso"]
            if barra["color_desde"] != barra["color_hasta"]:
                barra["color"] = mezclar(barra["color_desde"], barra["color_hasta"], suave)
            self._colocar(barra)
        suave = entrada_salida(t)
        self.foco_actual = tuple(a + (b - a) * suave for a, b in zip(self.foco_desde, self.foco_hacia))
        self.progreso_pista = suave
        self._pintar_banda()
        self._pintar_pista()

    def celebrar(self):
        """Ola pequena sobre las barras cuando el arreglo queda ordenado."""
        n = max(1, len(self.barras))
        if n > self.MAX_ANIMADAS:
            return

        def cuadro(t):
            for i, barra in enumerate(self.barras):
                local = min(1.0, max(0.0, t * 1.5 - 0.5 * i / n))
                barra["salto"] = math.sin(math.pi * local) * self.app.px(12)
                self._colocar(barra)
        self.app.animador.iniciar(self, 800, cuadro, lineal)

    def _medir(self):
        px = self.app.px
        n = max(1, len(self.barras))
        ancho, alto = self.winfo_width(), self.winfo_height()
        self.x0 = px(12)
        self.paso_x = (ancho - 2 * self.x0) / n
        self.ancho_barra = max(1.0, self.paso_x * (0.76 if n <= 80 else 0.92))
        self.pie = alto - px(60)
        fondo = self.pie - (px(20) if self.minimo < 0 else 0)     # lugar para la etiqueta de la barra negativa
        self.escala = (fondo - px(36)) / ((self.maximo - self.minimo) or 1)
        self.base = fondo + self.minimo * self.escala

    def _x(self, posicion):
        return self.x0 + posicion * self.paso_x

    def _colocar(self, barra):
        centro = self._x(barra["pos"] + 0.5)
        medio = self.ancho_barra / 2
        pie = self.base - barra["salto"]
        tope = pie - barra["valor"] * self.escala * barra["factor"]
        self.coords(barra["rect"], centro - medio, tope, centro + medio, pie)
        if barra["pintado"] != barra["color"]:
            barra["pintado"] = barra["color"]
            self.itemconfigure(barra["rect"], fill=barra["color"])
        if barra["texto"]:
            separacion = self.app.px(10)
            self.coords(barra["texto"], centro, tope - separacion if barra["valor"] >= 0 else tope + separacion)

    def _pintar_banda(self):
        inicio, fin = self.foco_actual
        self.coords(self.banda, self._x(inicio), self.app.px(6), self._x(fin), self.pie + 1)

    def _pintar_pista(self):
        """Debajo de las barras: los runs de la pila. Al fusionar, un run crece sobre el otro."""
        self.delete("pista")
        px = self.app.px
        y = self.pie + px(20)
        alto = px(13)
        letra = self.app.fuente(11, "bold")
        for inicio, fin in self.segmentos:
            fin_anterior = self.segmentos_desde.get(inicio, inicio)
            fin_visible = fin_anterior + (fin - fin_anterior) * self.progreso_pista
            x0, x1 = self._x(inicio) + 1, self._x(fin_visible) - 1
            if x1 - x0 < 1:
                continue
            activo = inicio <= self.foco_hacia[0] < fin
            color = self.color_foco if activo else AZUL_PALIDO
            self.create_rectangle(x0, y, x1, y + alto, fill=color, outline="", tags="pista")
            if letra.measure("00") < x1 - x0:
                claro = activo and color != DORADO
                self.create_text((x0 + x1) / 2, y + alto / 2, text=str(fin - inicio), font=letra,
                                 fill="white" if claro else TINTA, tags="pista")
        self.create_text(self.x0 + 1, y + alto + px(3), text=self.titulo_pista, anchor="nw", font=self.app.fuente(11),
                         fill=TEXTO_SUAVE, tags="pista")

    def _repintar(self):
        if not self.barras:
            return
        self._medir()
        self.delete("fijo")
        self.create_line(self.x0, self.base, self.winfo_width() - self.x0, self.base, fill=BORDE_FUERTE, tags="fijo")
        if len(self.barras) <= 40:
            for i in range(len(self.barras)):
                self.create_text(self._x(i + 0.5), self.pie + self.app.px(9), text=str(i), font=self.app.fuente(11),
                                 fill=TEXTO_SUAVE, tags="fijo")
        for barra in self.barras:
            self._colocar(barra)
        self._pintar_banda()
        self._pintar_pista()
        self.tag_lower(self.banda)


class Cancelado(Exception):
    """El usuario pidio detener la medicion."""


# ---------------------------------------------------------------------------
# Interfaz grafica
# ---------------------------------------------------------------------------
class AplicacionOrdenamiento(tk.Tk):
    def __init__(self):
        super().__init__()
        self.withdraw()              # no mostrar la ventana a medio construir
        self.title("Producto didáctico de ordenamiento - David Santiago Carrillo Salamanca")
        self.configure(bg=FONDO)
        self.esc = max(1.0, self.winfo_fpixels("1i") / 96)      # pantallas de alta densidad
        self._fuentes = {}
        self.familia, self.familia_mono = self._elegir_familias()
        self.animador = Animador(self)
        self.margen = self.px(20)
        self.algoritmo = tk.StringVar(value="TimSort")
        self.botones_trabajo = []
        self.trabajando = False
        self.cancelacion = threading.Event()
        self.traza_actual = []
        self.arreglo_actual = None
        self.minrun_actual = None
        self.paso_actual = 0
        self.velocidad = 1
        self.reproduciendo = False
        self.turno_reproduccion = None
        self.seccion_actual = 0
        self.ficha_abierta = False
        self.ficha_x = 0.0
        self.aviso_y = 0.0
        self.turno_aviso = None
        self.puntos_demo_n = []
        self.puntos_demo_tiempo = []

        self._ajustar_ventana()
        self._crear_estilo()
        self._poner_icono()
        self._crear_columna()
        self._crear_principal()
        self.pestana_algoritmo, self.pestana_temporal, self.pestana_rendimiento, self.pestana_demo, \
            self.pestana_calidad, self.pestana_pseudocodigo, self.pestana_comparacion = \
            [self._crear_seccion() for _ in SECCIONES]
        self._crear_pestana_algoritmo()
        self._crear_pestana_temporal()
        self._crear_pestana_rendimiento()
        self._crear_pestana_demo()
        self._crear_pestana_calidad()
        self._crear_pestana_pseudocodigo()
        self._crear_pestana_comparacion()
        self._crear_ficha()
        self._crear_aviso()

        self.secciones[0].place(x=0, y=0, relwidth=1, relheight=1)
        self.bind("<KeyPress>", self._tecla)
        self.bind_all("<Button-1>", self._clic_global, add="+")
        self.bind_all("<MouseWheel>", self._rueda)
        self.bind_all("<Button-4>", self._rueda)
        self.bind_all("<Button-5>", self._rueda)
        self._cambiar_algoritmo()
        self.deiconify()
        self.focus_set()
        self.after(120, self._cargar_ejemplo)

    def px(self, valor):
        return max(1, round(valor * self.esc)) if valor else 0

    def fuente(self, tamano, peso="normal", mono=False):
        """Fuentes en pixeles: en puntos, un mismo tamano se ve distinto en macOS y en Windows."""
        clave = (tamano, peso, mono)
        if clave not in self._fuentes:
            self._fuentes[clave] = tkfont.Font(root=self, family=self.familia_mono if mono else self.familia,
                                               size=-self.px(tamano), weight=peso)
        return self._fuentes[clave]

    def _elegir_familias(self):
        disponibles = set(tkfont.families(self))

        def elegir(candidatas, respaldo):
            for familia in candidatas:
                if familia in disponibles:
                    return familia
            return tkfont.nametofont(respaldo).actual("family")

        interfaz = () if sys.platform == "darwin" else ("Segoe UI", "Ubuntu", "Cantarell", "Noto Sans", "DejaVu Sans")
        return elegir(interfaz, "TkDefaultFont"), elegir(
            ("Cascadia Mono", "Consolas", "Menlo", "Ubuntu Mono", "DejaVu Sans Mono"), "TkFixedFont")

    def _ajustar_ventana(self):
        """La ventana se calcula con la pantalla de cada equipo, no con un tamano fijo."""
        pantalla_x, pantalla_y = self.winfo_screenwidth(), self.winfo_screenheight()
        ancho = min(self.px(1500), int(pantalla_x * 0.94))
        alto = min(self.px(940), int(pantalla_y * 0.88))
        self.geometry(f"{ancho}x{alto}+{(pantalla_x - ancho) // 2}+{max(0, (pantalla_y - alto) // 3)}")
        self.minsize(min(self.px(980), ancho), min(self.px(620), alto))

    def _poner_icono(self):
        icono = tk.PhotoImage(master=self, width=32, height=32)
        icono.put(AZUL_OSCURO, to=(0, 0, 32, 32))
        for i, (alto, color) in enumerate(((9, "white"), (15, "white"), (22, DORADO))):
            icono.put(color, to=(5 + i * 8, 27 - alto, 11 + i * 8, 27))
        self.iconphoto(True, icono)
        self._icono = icono

    def _crear_estilo(self):
        estilo = ttk.Style(self)
        estilo.theme_use("clam")
        px = self.px
        estilo.configure("Treeview", background=TARJETA, fieldbackground=TARJETA, foreground=TINTA, rowheight=px(25),
                         font=self.fuente(12), borderwidth=0, relief="flat")
        estilo.layout("Treeview", [("Treeview.treearea", {"sticky": "nswe"})])
        estilo.map("Treeview", background=[("selected", "#DCE8F7")], foreground=[("selected", TINTA)])
        estilo.configure("Treeview.Heading", background="#EDF1F7", foreground=TEXTO_SUAVE, font=self.fuente(12, "bold"),
                         relief="flat", borderwidth=0, padding=(px(6), px(4)))
        estilo.map("Treeview.Heading", background=[("active", "#E3E9F3")])
        estilo.configure("TCombobox", foreground=TINTA, fieldbackground="white", background="white", arrowcolor=AZUL_OSCURO,
                         bordercolor=BORDE_FUERTE, lightcolor="white", darkcolor="white", padding=(px(6), 0))
        estilo.map("TCombobox", fieldbackground=[("readonly", "white")], selectbackground=[("readonly", "white")],
                   selectforeground=[("readonly", TINTA)], foreground=[("readonly", TINTA)],
                   background=[("readonly", "white"), ("active", "#EDF2F9")], bordercolor=[("focus", AZUL)])
        estilo.configure("Vertical.TScrollbar", background=BORDE_FUERTE, troughcolor=FONDO, bordercolor=FONDO,
                         lightcolor=BORDE_FUERTE, darkcolor=BORDE_FUERTE, arrowcolor=TEXTO_SUAVE, gripcount=0)
        self.option_add("*TCombobox*Listbox.font", self.fuente(13))
        self.option_add("*TCombobox*Listbox.background", "white")
        self.option_add("*TCombobox*Listbox.foreground", TINTA)
        self.option_add("*TCombobox*Listbox.selectBackground", AZUL_OSCURO)
        self.option_add("*TCombobox*Listbox.selectForeground", "white")

    # ========================= ESTRUCTURA GENERAL ============================
    def _crear_columna(self):
        px = self.px
        columna = tk.Frame(self, bg=COLUMNA, width=px(244))
        columna.pack(side="left", fill="y")
        columna.pack_propagate(False)

        marca = tk.Frame(columna, bg=COLUMNA)
        marca.pack(fill="x", padx=px(16), pady=(px(16), px(10)))
        logo = tk.Canvas(marca, width=px(30), height=px(30), bg=COLUMNA, highlightthickness=0)
        logo.pack(side="left", padx=(0, px(10)))
        for i, (alto, color) in enumerate(((11, "white"), (19, "white"), (29, DORADO))):
            logo.create_rectangle(px(1 + i * 10), px(30 - alto), px(8 + i * 10), px(30), fill=color, outline="")
        textos = tk.Frame(marca, bg=COLUMNA)
        textos.pack(side="left")
        tk.Label(textos, text="Ordenamiento", bg=COLUMNA, fg="white", font=self.fuente(16, "bold"), anchor="w").pack(fill="x")
        tk.Label(textos, text="Producto didáctico y comparativo", bg=COLUMNA, fg=COLUMNA_TEXTO, font=self.fuente(11),
                 anchor="w").pack(fill="x")

        self._titulo_columna(columna, "MÉTODO")
        filas = [{"texto": nombre, "detalle": datos["rol"], "color": COLOR_METODO[nombre]} for nombre, datos in ALGORITMOS.items()]
        self.menu_metodos = Menu(columna, self, filas, self._elegir_metodo, alto_fila=38)
        self.menu_metodos.pack(fill="x")

        self._titulo_columna(columna, "SECCIONES")
        filas = [{"texto": titulo, "numero": str(i)} for i, (titulo, _) in enumerate(SECCIONES, 1)]
        self.menu_secciones = Menu(columna, self, filas, self._ir_a_seccion, alto_fila=35)
        self.menu_secciones.pack(fill="x")

        pie = tk.Frame(columna, bg=COLUMNA)
        pie.pack(side="bottom", fill="x", padx=px(18), pady=px(12))
        tk.Label(pie, text="← →  pasos   ·   Espacio  reproducir\n1-7  secciones   ·   F  ficha", bg=COLUMNA, fg=COLUMNA_TEXTO,
                 font=self.fuente(11), justify="left", anchor="w").pack(fill="x")
        tk.Label(pie, text="David Santiago Carrillo Salamanca", bg=COLUMNA, fg="white", font=self.fuente(11, "bold"),
                 anchor="w").pack(fill="x", pady=(px(6), 0))

    def _titulo_columna(self, padre, texto):
        tk.Label(padre, text=texto, bg=COLUMNA, fg=COLUMNA_TEXTO, font=self.fuente(11, "bold"), anchor="w").pack(
            fill="x", padx=self.px(20), pady=(self.px(10), self.px(4)))

    def _crear_principal(self):
        px = self.px
        self.principal = tk.Frame(self, bg=FONDO)
        self.principal.pack(side="left", fill="both", expand=True)

        barra = tk.Frame(self.principal, bg=FONDO)
        barra.pack(fill="x", padx=self.margen, pady=(px(14), px(6)))
        self.boton_ficha = Boton(barra, self, "Ficha del método", self._alternar_ficha)
        self.boton_ficha.pack(side="right")
        self.boton_cancelar = Boton(barra, self, "Cancelar", self._cancelar_trabajo)
        self.estado = tk.Label(barra, text="", bg=FONDO, fg=TEXTO_SUAVE, font=self.fuente(12))
        self.estado.pack(side="right", padx=px(12))
        textos = tk.Frame(barra, bg=FONDO)
        textos.pack(side="left", fill="x", expand=True)
        self.titulo_seccion = tk.Label(textos, text=SECCIONES[0][0], bg=FONDO, fg=TINTA, font=self.fuente(22, "bold"), anchor="w")
        self.titulo_seccion.pack(fill="x")
        self.subtitulo_seccion = tk.Label(textos, text=SECCIONES[0][1], bg=FONDO, fg=TEXTO_SUAVE, font=self.fuente(13), anchor="w")
        self.subtitulo_seccion.pack(fill="x")

        self.progreso = BarraProgreso(self.principal, self)
        self.progreso.pack(fill="x", padx=self.margen)
        self.escenario = tk.Frame(self.principal, bg=FONDO)
        self.escenario.pack(fill="both", expand=True, pady=(px(4), px(8)))
        self.secciones = []

    def _crear_seccion(self):
        seccion = Seccion(self.escenario, self)
        self.secciones.append(seccion)
        return seccion.cuerpo

    def _tarjeta(self, padre, titulo=None):
        marco = tk.Frame(padre, bg=TARJETA, highlightbackground=BORDE, highlightcolor=BORDE, highlightthickness=1)
        if titulo:
            tk.Label(marco, text=titulo, bg=TARJETA, fg=TINTA, font=self.fuente(13, "bold"), anchor="w").pack(
                fill="x", padx=self.px(12), pady=(self.px(8), self.px(2)))
        return marco

    def _fila_controles(self, padre):
        tarjeta = self._tarjeta(padre)
        tarjeta.pack(fill="x", padx=self.margen, pady=(self.px(4), self.px(6)))
        fila = FilaFluida(tarjeta, self)
        fila.pack(fill="x", padx=self.px(14), pady=self.px(11))
        return fila

    def _mensaje(self, padre, texto=""):
        etiqueta = Parrafo(padre, text=texto, bg=FONDO, fg=TINTA, font=self.fuente(13, "bold"))
        etiqueta.pack(fill="x", padx=self.margen, pady=(self.px(2), self.px(4)))
        return etiqueta

    def _boton_trabajo(self, padre, texto, comando, estilo="secundario"):
        """Boton que lanza una medicion: se apaga mientras haya otra en curso."""
        boton = Boton(padre, self, texto, comando, estilo)
        self.botones_trabajo.append(boton)
        return boton

    def _fila_graficas(self, padre, cantidad, vacio, alto=230):
        fila = tk.Frame(padre, bg=FONDO)
        fila.pack(fill="both", expand=True, padx=self.margen, pady=self.px(4))
        fila.rowconfigure(0, weight=1)
        graficas = []
        for i in range(cantidad):
            fila.columnconfigure(i, weight=1, uniform="graficas")
            tarjeta = self._tarjeta(fila)
            tarjeta.grid(row=0, column=i, sticky="nsew", padx=(self.px(10) if i else 0, 0))
            grafica = Grafica(tarjeta, self, vacio, alto)
            grafica.pack(fill="both", expand=True, padx=self.px(4), pady=self.px(4))
            graficas.append(grafica)
        return graficas

    def _crear_tabla(self, padre, columnas, anchos, alto=6):
        tabla = ttk.Treeview(padre, columns=columnas, show="headings", height=alto, selectmode="none")
        for columna, ancho in zip(columnas, anchos):
            tabla.heading(columna, text=columna, anchor="e")
            tabla.column(columna, width=self.px(ancho), minwidth=self.px(50), anchor="e", stretch=True)
        tabla.heading(columnas[0], anchor="w")
        tabla.column(columnas[0], anchor="w")
        tabla.tag_configure("par", background="#F6F8FC")
        tabla.tag_configure("bien", foreground=VERDE)
        tabla.tag_configure("mal", foreground=ROJO)
        return tabla

    def _tabla_en_tarjeta(self, padre, titulo, columnas, anchos, alto=6):
        tarjeta = self._tarjeta(padre, titulo)
        tarjeta.pack(fill="x", padx=self.margen, pady=self.px(4))
        tabla = self._crear_tabla(tarjeta, columnas, anchos, alto)
        tabla.pack(fill="x", padx=self.px(8), pady=(self.px(2), self.px(8)))
        return tabla

    def _llenar(self, tabla, filas, marcas=None):
        tabla.delete(*tabla.get_children())
        for i, fila in enumerate(filas):
            etiquetas = ("par",) if i % 2 else ()
            if marcas:
                etiquetas += (marcas[i],)
            tabla.insert("", "end", values=fila, tags=etiquetas)

    def _crear_ficha(self):
        px = self.px
        self.ancho_ficha = px(360)
        self.ficha_x = float(self.ancho_ficha)
        self.cajon = tk.Frame(self.principal, bg=TARJETA, highlightthickness=1, highlightbackground=BORDE_FUERTE,
                              highlightcolor=BORDE_FUERTE)
        cabecera = tk.Frame(self.cajon, bg=TARJETA)
        cabecera.pack(fill="x", padx=px(18), pady=(px(16), px(6)))
        BotonIcono(cabecera, self, "cerrar", self._alternar_ficha, lado=30).pack(side="right", anchor="n")
        self.ficha_titulo = tk.Label(cabecera, bg=TARJETA, fg=TINTA, font=self.fuente(20, "bold"), anchor="w")
        self.ficha_titulo.pack(fill="x")
        self.ficha_rol = tk.Label(cabecera, bg=TARJETA, fg=TEXTO_SUAVE, font=self.fuente(13), anchor="w")
        self.ficha_rol.pack(fill="x")
        barra = ttk.Scrollbar(self.cajon)
        barra.pack(side="right", fill="y", pady=px(6))
        self.ficha = tk.Text(self.cajon, wrap="word", bg=TARJETA, fg=TINTA, relief="flat", bd=0, highlightthickness=0,
                             cursor="arrow", padx=px(18), pady=px(4), yscrollcommand=barra.set, font=self.fuente(13),
                             spacing1=px(1), spacing3=px(3), width=10, height=5)
        self.ficha.pack(side="left", fill="both", expand=True)
        barra.config(command=self.ficha.yview)
        self.ficha.tag_configure("titulo", font=self.fuente(14, "bold"), foreground=AZUL_OSCURO, spacing1=px(12), spacing3=px(4))
        self.ficha.tag_configure("dato", foreground=TEXTO_SUAVE)

    def _crear_aviso(self):
        self.aviso = tk.Frame(self.principal, bg=TINTA)
        self.aviso_marca = tk.Frame(self.aviso, bg=AZUL_CLARO, width=self.px(5))
        self.aviso_marca.pack(side="left", fill="y")
        self.aviso_texto = tk.Label(self.aviso, bg=TINTA, fg="white", font=self.fuente(13), justify="left",
                                    wraplength=self.px(620))
        self.aviso_texto.pack(side="left", padx=self.px(14), pady=self.px(10))

    def avisar(self, texto, tipo="info"):
        """Mensaje que entra desde abajo y se va solo: no interrumpe como una ventana emergente."""
        self.aviso_marca.config(bg={"info": AZUL_CLARO, "ok": VERDE, "error": ROJO}[tipo])
        self.aviso_texto.config(text=texto)
        if self.turno_aviso is not None:
            self.after_cancel(self.turno_aviso)
        self.turno_aviso = self.after(4200, self._ocultar_aviso)
        self._mover_aviso(-self.px(20))

    def _ocultar_aviso(self):
        self.turno_aviso = None
        self._mover_aviso(self.px(70), lambda: self.aviso.place_forget())

    def _mover_aviso(self, hasta, al_final=None):
        desde = self.aviso_y if self.aviso.winfo_ismapped() else float(self.px(70))
        self.aviso.place(relx=0.5, rely=1.0, anchor="s", y=round(desde))
        self.aviso.lift()

        def cuadro(t):
            self.aviso_y = desde + (hasta - desde) * t
            self.aviso.place_configure(y=round(self.aviso_y))
        self.animador.iniciar("aviso", 280, cuadro, salida_cubica, al_final)

    def _alternar_ficha(self, abrir=None):
        abrir = not self.ficha_abierta if abrir is None else abrir
        if abrir == self.ficha_abierta:
            return
        self.ficha_abierta = abrir
        desde, hasta = self.ficha_x, 0.0 if abrir else float(self.ancho_ficha)
        self.cajon.place(relx=1.0, rely=0, anchor="ne", relheight=1, width=self.ancho_ficha, x=round(desde))
        self.cajon.lift()

        def cuadro(t):
            self.ficha_x = desde + (hasta - desde) * t
            self.cajon.place_configure(x=round(self.ficha_x))

        def al_final():
            if not self.ficha_abierta:
                self.cajon.place_forget()
        self.animador.iniciar("ficha", 280, cuadro, salida_cubica, al_final)

    def _ir_a_seccion(self, indice):
        """La seccion nueva entra con un deslizamiento corto en la direccion del menu."""
        if indice == self.seccion_actual:
            return
        self._pausar()
        anterior, self.seccion_actual = self.seccion_actual, indice
        self.menu_secciones.elegir(indice)
        self.titulo_seccion.config(text=SECCIONES[indice][0])
        self.subtitulo_seccion.config(text=SECCIONES[indice][1])
        nueva = self.secciones[indice]
        self.secciones[anterior].place_forget()
        salto = self.px(30) * (1 if indice > anterior else -1)
        nueva.place(x=0, y=salto, relwidth=1, relheight=1)
        self.animador.iniciar("seccion", 260, lambda t: nueva.place_configure(y=round(salto * (1 - t))))

    def _elegir_metodo(self, indice):
        if self.trabajando:
            self.avisar("Hay una medición en curso: espera a que termine o cancélala.", "error")
            return
        self.menu_metodos.elegir(indice)
        self.algoritmo.set(list(ALGORITMOS)[indice])
        self._cambiar_algoritmo()

    def _tecla(self, evento):
        widget = evento.widget
        if isinstance(widget, (str, tk.Entry, tk.Text, Boton)):
            return                   # escribir un numero en un campo no debe cambiar de seccion
        tecla = evento.keysym
        if tecla in tuple("1234567"):
            self._ir_a_seccion(int(tecla) - 1)
        elif tecla in ("f", "F"):
            self._alternar_ficha()
        elif tecla == "Escape":
            self._alternar_ficha(False)
        elif self.seccion_actual == 0:
            if tecla == "Right":
                self._cambiar_paso(1)
            elif tecla == "Left":
                self._cambiar_paso(-1)
            elif tecla == "space":
                self._alternar_reproduccion()
            elif tecla == "Home":
                self._ir_a_paso(0)
            elif tecla == "End":
                self._ir_a_paso(len(self.traza_actual) - 1)

    def _clic_global(self, evento):
        """Clic fuera de un campo: suelta el foco para que vuelvan a servir los atajos."""
        if not isinstance(evento.widget, (str, tk.Entry)):
            self.focus_set()

    def _rueda(self, evento):
        if isinstance(evento.widget, (str, tk.Text, ttk.Treeview)):
            return
        if evento.num == 4:
            unidades = -1
        elif evento.num == 5:
            unidades = 1
        else:
            delta = evento.delta / 120 if abs(evento.delta) >= 120 else evento.delta     # cambia segun el sistema
            unidades = -int(math.copysign(max(1, abs(delta)), delta))
        self.secciones[self.seccion_actual].desplazar(unidades)

    # ===================== MEDICIONES EN SEGUNDO PLANO =======================
    def _en_segundo_plano(self, mensaje, trabajo, al_terminar):
        """Corre trabajo(avance) en un hilo para que la ventana no se congele.
        al_terminar(resultado) vuelve a correr en el hilo de la ventana."""
        if self.trabajando:
            self.avisar("Ya hay una medición en curso.", "error")
            return
        self.trabajando = True
        self.cancelacion.clear()
        for boton in self.botones_trabajo:
            boton.habilitar(False)
        self.boton_cancelar.habilitar(True)
        self.boton_cancelar.pack(side="right", before=self.estado)
        self.estado.config(text=mensaje)
        self.progreso.poner(0.0)
        cola = queue.Queue()

        def avance(fraccion):
            if self.cancelacion.is_set():
                raise Cancelado
            cola.put(("avance", fraccion))

        def correr():
            try:
                cola.put(("listo", trabajo(avance)))
            except Cancelado:
                cola.put(("cancelado", None))
            except Exception as error:
                cola.put(("error", error))

        threading.Thread(target=correr, daemon=True).start()
        self._vigilar(cola, mensaje, al_terminar, self.seccion_actual)

    def _vigilar(self, cola, mensaje, al_terminar, origen):
        fraccion = None
        while True:
            try:
                tipo, valor = cola.get_nowait()
            except queue.Empty:
                break
            if tipo == "avance":
                fraccion = valor
                continue
            self._fin_trabajo()
            if tipo == "listo":
                if origen != self.seccion_actual:
                    self.avisar(f"Medición lista: mira la sección {SECCIONES[origen][0]}.", "ok")
                al_terminar(valor)
            elif tipo == "cancelado":
                self.avisar("Medición cancelada.")
            else:
                self.avisar(f"Algo salió mal: {valor}", "error")
            return
        if fraccion is not None:
            self.progreso.poner(fraccion)
            self.estado.config(text=f"{mensaje} {round(fraccion * 100)} %")
        self.after(120, self._vigilar, cola, mensaje, al_terminar, origen)

    def _fin_trabajo(self):
        self.trabajando = False
        for boton in self.botones_trabajo:
            boton.habilitar(True)
        self.boton_cancelar.pack_forget()
        self.estado.config(text="")
        self.progreso.poner(None)

    def _cancelar_trabajo(self):
        self.cancelacion.set()
        self.boton_cancelar.habilitar(False)
        self.estado.config(text="Cancelando al terminar esta repetición...")

    def _error(self, campo, texto):
        """Reemplaza a las ventanas de error: marca el campo y explica que paso."""
        campo.marcar_error()
        self.avisar(texto, "error")

    # ======================= CAMBIO DE METODO ===============================
    def _mostrar_ficha(self):
        nombre = self.algoritmo.get()
        datos = ALGORITMOS[nombre]
        self.boton_ficha.cambiar_texto(f"Ficha de {nombre}")
        self.ficha_titulo.config(text=nombre)
        self.ficha_rol.config(text=f"Método {datos['rol'].lower()}")
        self.ficha.config(state="normal")
        self.ficha.delete("1.0", "end")
        self.ficha.insert("end", "Historia\n", "titulo")
        self.ficha.insert("end", datos["historia"] + "\n")
        self.ficha.insert("end", "Categorías\n", "titulo")
        self.ficha.insert("end", "".join(f"•  {c}\n" for c in datos["categorias"]))
        self.ficha.insert("end", "Características\n", "titulo")
        self.ficha.insert("end", "".join(f"•  {c}\n" for c in datos["caracteristicas"]))
        self.ficha.insert("end", "Rendimiento Big O\n", "titulo")
        for caso, valor in datos["big_o"].items():
            self.ficha.insert("end", f"{caso}: ", "dato")
            self.ficha.insert("end", f"{valor}\n")
        self.ficha.insert("end", "Estable: ", "dato")
        self.ficha.insert("end", f"{datos['estable']}\n")
        self.ficha.insert("end", "Adaptativo: ", "dato")
        self.ficha.insert("end", f"{datos['adaptativo']}\n")
        self.ficha.config(state="disabled")

    def _cambiar_algoritmo(self):
        """Se llama al elegir un metodo: todas las secciones pasan a usarlo."""
        nombre = self.algoritmo.get()
        datos = ALGORITMOS[nombre]
        self._mostrar_ficha()
        self._poner_leyenda()
        self.entrada_minrun_algoritmo.habilitar(nombre != "Insertion Sort")
        if self.arreglo_actual:        # la misma lista con otro metodo: asi se pueden comparar
            self._cargar_lista(self.arreglo_actual, self.minrun_actual)
        for tabla in (self.tabla_temporal, self.tabla_galope, self.tabla_demo, self.tabla_calidad):
            tabla.delete(*tabla.get_children())
        for grafica in (self.grafica_comparaciones, self.grafica_movimientos, self.grafica_tiempo, self.grafica_casos_comp,
                        self.grafica_casos_tiempo, self.grafica_calidad_curvas, self.grafica_calidad_razon):
            grafica.vaciar()
        for indicador in self.indicadores_calidad + self.indicadores_pseudocodigo:
            indicador.limpiar()
        self._reiniciar_demo()    # para no mezclar puntos de dos metodos en la misma grafica
        self.etiqueta_temporal.config(text=(f"{nombre}: f(n) = {datos['texto_mejor']} en el mejor caso "
                                            f"({datos['big_o']['Mejor']}) y f(n) ≈ {datos['texto_peor']} en el peor "
                                            f"caso ({datos['big_o']['Peor']})."))
        self.tabla_temporal.heading("Mejor f(n)", text=f"Mejor: {datos['texto_mejor']}")
        self.tabla_temporal.heading("Peor f(n)", text=f"Peor: {datos['texto_peor']}")
        self.etiqueta_rendimiento.config(text=f"{nombre}: compara el mismo n con distintos tipos de entrada.")
        self.etiqueta_calidad.config(text=f"{nombre}: aún no se ha validado.")
        self.etiqueta_pseudocodigo.config(text=f"{nombre}: aún no se ha validado el pseudocódigo.")
        self._escribir_codigo(self.texto_pseudocodigo, datos["pseudocodigo"],
                              r"\b(ALGORITMO|MIENTRAS|HACER|PARA|HASTA|SI|ENTONCES|FIN|Y)\b")
        self._escribir_codigo(self.texto_python, pseudocodigo_a_python(datos["pseudocodigo"]),
                              r"\b(def|while|for|in|range|if|and)\b")

    def _limite(self, n):
        limite = ALGORITMOS[self.algoritmo.get()]["limite_n"]
        return n if limite is None else min(n, limite)

    def _limitar(self, n):
        """Insertion Sort no aguanta los tamanos grandes: se recorta n para el y se avisa."""
        limitado = self._limite(n)
        if limitado != n:
            self.avisar(f"{self.algoritmo.get()} solo se mide hasta n = {miles(limitado)}: se usó ese valor.")
        return limitado

    # ========================= ALGORITMO BASE ============================
    def _crear_pestana_algoritmo(self):
        px = self.px
        cuerpo = self.pestana_algoritmo
        fila = self._fila_controles(cuerpo)
        generar = self._generar_pasos_algoritmo
        self.entrada_lista_algoritmo = fila.agregar(
            Campo(fila, self, "Tu lista (opcional, separada por comas)", "", 16, generar), expandir=True)
        self.entrada_tam_aleatorio_algoritmo = fila.agregar(Campo(fila, self, "Tamaño aleatorio", "16", 8, generar))
        self.entrada_minrun_algoritmo = fila.agregar(Campo(fila, self, "minrun (vacío = auto)", "4", 9, generar))
        fila.agregar(Boton(fila, self, "Generar pasos", generar, "primario"))
        fila.agregar(Boton(fila, self, "Ejemplo", self._cargar_ejemplo))
        fila.agregar(self._boton_trabajo(fila, "Verificar (400)", self._verificar))

        tarjeta = self._tarjeta(cuerpo)
        tarjeta.pack(fill="both", expand=True, padx=self.margen, pady=px(4))
        cabecera = tk.Frame(tarjeta, bg=TARJETA)
        cabecera.pack(fill="x", padx=px(14), pady=(px(10), px(4)))
        self.insignia_paso = tk.Label(cabecera, text=" INICIO ", bg=AZUL_CLARO, fg="white", font=self.fuente(12, "bold"),
                                      padx=px(6), pady=px(2))
        self.insignia_paso.pack(side="left")
        self.contador_paso = tk.Label(cabecera, text="", bg=TARJETA, fg=TINTA, font=self.fuente(13, "bold"))
        self.contador_paso.pack(side="left", padx=px(10))
        self.leyenda_paso = tk.Frame(cabecera, bg=TARJETA)
        self.leyenda_paso.pack(side="right")
        self.etiqueta_paso = Parrafo(tarjeta, text="", bg=TARJETA, fg=TINTA, font=self.fuente(14), height=2)
        self.etiqueta_paso.pack(fill="x", padx=px(14))

        mando = tk.Frame(tarjeta, bg=TARJETA)
        mando.pack(side="bottom", fill="x", padx=px(14), pady=(px(4), px(12)))
        for icono, comando in (("primero", lambda: self._ir_a_paso(0)), ("anterior", lambda: self._cambiar_paso(-1))):
            BotonIcono(mando, self, icono, comando).pack(side="left", padx=(0, px(6)))
        self.boton_reproducir = BotonIcono(mando, self, "reproducir", self._alternar_reproduccion, "primario", lado=42)
        self.boton_reproducir.pack(side="left", padx=(0, px(6)))
        for icono, comando in (("siguiente", lambda: self._cambiar_paso(1)),
                               ("ultimo", lambda: self._ir_a_paso(len(self.traza_actual) - 1))):
            BotonIcono(mando, self, icono, comando).pack(side="left", padx=(0, px(6)))
        Segmentos(mando, self, ("0,5x", "1x", "2x", "4x"), 1, self._cambiar_velocidad).pack(side="right")
        tk.Label(mando, text="Velocidad", bg=TARJETA, fg=TEXTO_SUAVE, font=self.fuente(12)).pack(side="right", padx=px(8))
        self.linea_tiempo = LineaTiempo(mando, self, self._ir_a_paso)
        self.linea_tiempo.pack(side="left", fill="x", expand=True, padx=px(10))

        self.lienzo_barras = LienzoBarras(tarjeta, self)
        self.lienzo_barras.pack(fill="both", expand=True, padx=px(6), pady=(px(2), 0))

    def _poner_leyenda(self):
        for hijo in self.leyenda_paso.winfo_children():
            hijo.destroy()
        if self.algoritmo.get() == "Insertion Sort":
            elementos = ((AZUL, "Zona ordenada"), (DORADO, "Recién insertado"))
        else:
            elementos = ((AZUL, "Run ascendente"), (DORADO, "Run invertido"), (AZUL_OSCURO, "Fusión"))
        for color, texto in elementos:
            tk.Frame(self.leyenda_paso, bg=color, width=self.px(11), height=self.px(11)).pack(
                side="left", padx=(self.px(12), self.px(5)))
            tk.Label(self.leyenda_paso, text=texto, bg=TARJETA, fg=TEXTO_SUAVE, font=self.fuente(12)).pack(side="left")

    def _cargar_ejemplo(self):
        # Mismo arreglo de la diapositiva "Ejemplo paso a paso con 12 elementos"
        self.entrada_lista_algoritmo.set("2, 5, 7, 9, 8, 6, 3, 1, 4, 10, 11, 12")
        self.entrada_minrun_algoritmo.habilitar(True)
        self.entrada_minrun_algoritmo.set("4")
        self.entrada_minrun_algoritmo.habilitar(self.algoritmo.get() != "Insertion Sort")
        self._generar_pasos_algoritmo()

    def _generar_pasos_algoritmo(self):
        texto_lista = self.entrada_lista_algoritmo.get().strip()
        if texto_lista:
            try:
                arreglo = [int(v.strip()) for v in texto_lista.split(",") if v.strip()]
            except ValueError:
                self._error(self.entrada_lista_algoritmo, "La lista debe contener solo números enteros separados por coma.")
                return
            if len(arreglo) < 2:
                self._error(self.entrada_lista_algoritmo, "Escribe al menos 2 números.")
                return
            if len(arreglo) > MAX_PASO_A_PASO:
                self._error(self.entrada_lista_algoritmo, f"El paso a paso admite hasta {MAX_PASO_A_PASO} números.")
                return
        else:
            try:
                tam = leer_entero(self.entrada_tam_aleatorio_algoritmo.get())
                if not 2 <= tam <= MAX_PASO_A_PASO:
                    raise ValueError
            except ValueError:
                self._error(self.entrada_tam_aleatorio_algoritmo,
                            f"El tamaño de la lista aleatoria debe ser un entero entre 2 y {MAX_PASO_A_PASO}.")
                return
            arreglo = list(range(1, tam + 1))
            random.shuffle(arreglo)

        texto_minrun = self.entrada_minrun_algoritmo.get().strip()
        if texto_minrun:
            try:
                minrun = leer_entero(texto_minrun)
                if minrun < 1:
                    raise ValueError
            except ValueError:
                self._error(self.entrada_minrun_algoritmo, "minrun debe ser un entero mayor o igual a 1 (o dejarlo vacío).")
                return
        else:
            minrun = calcular_minrun(len(arreglo))
        self._cargar_lista(arreglo, minrun)

    def _cargar_lista(self, arreglo, minrun):
        self._pausar()
        self.arreglo_actual, self.minrun_actual = arreglo, minrun
        nombre = self.algoritmo.get()
        self.traza_actual = traza_de(nombre, list(arreglo), minrun)
        self.paso_actual = 0
        titulo_pista = "Zona ordenada" if nombre == "Insertion Sort" else "Pila de runs (largo de cada uno)"
        self.lienzo_barras.cargar(self.traza_actual[0], titulo_pista)
        self.linea_tiempo.cargar([color_de_paso(paso) for paso in self.traza_actual])
        self._mostrar_textos_paso()

    def _mostrar_textos_paso(self):
        paso = self.traza_actual[self.paso_actual]
        total = len(self.traza_actual) - 1
        insignia, descripcion = describir_paso(paso, self.paso_actual == total)
        color = color_de_paso(paso)
        self.insignia_paso.config(text=insignia, bg=color, fg=TINTA if color == DORADO else "white")
        self.contador_paso.config(text=f"Paso {self.paso_actual} de {total}")
        self.etiqueta_paso.config(text=descripcion)

    def _cambiar_paso(self, delta):
        if not self.traza_actual:
            return
        indice = max(0, min(self.paso_actual + delta, len(self.traza_actual) - 1))
        if indice == self.paso_actual:
            return
        self.paso_actual = indice
        self._mostrar_textos_paso()
        self.linea_tiempo.marcar(indice)
        paso = self.traza_actual[indice]
        ola = {"fusion": 0.55, "run": 0.35}.get(paso["tipo"], 0.0) if delta > 0 else 0.0
        al_final = self.lienzo_barras.celebrar if delta > 0 and indice == len(self.traza_actual) - 1 else None
        self.lienzo_barras.ir_a(paso, DURACION_PASO / self.velocidad, ola, al_final)

    def _ir_a_paso(self, indice):
        """Salto directo (linea de tiempo, primero, ultimo): mas corto y sin ola."""
        self._pausar()
        if self.traza_actual and indice != self.paso_actual:
            self.paso_actual = indice
            self._mostrar_textos_paso()
            self.linea_tiempo.marcar(indice)
            self.lienzo_barras.ir_a(self.traza_actual[indice], 320)

    def _alternar_reproduccion(self):
        if self.reproduciendo:
            self._pausar()
        elif self.traza_actual:
            self.reproduciendo = True
            self.boton_reproducir.cambiar_icono("pausa")
            if self.paso_actual >= len(self.traza_actual) - 1:      # al final: vuelve a empezar
                self.paso_actual = 0
                self._mostrar_textos_paso()
                self.linea_tiempo.marcar(0)
                self.lienzo_barras.ir_a(self.traza_actual[0], 420)
                self.turno_reproduccion = self.after(600, self._avanzar_solo)
            else:
                self._avanzar_solo()

    def _avanzar_solo(self):
        self.turno_reproduccion = None
        if not self.reproduciendo:
            return
        self._cambiar_paso(1)
        if self.paso_actual >= len(self.traza_actual) - 1:
            self._pausar()
        else:
            espera = (DURACION_PASO + PAUSA_PASO) / self.velocidad
            self.turno_reproduccion = self.after(round(espera), self._avanzar_solo)

    def _pausar(self):
        self.reproduciendo = False
        if self.turno_reproduccion is not None:
            self.after_cancel(self.turno_reproduccion)
            self.turno_reproduccion = None
        if hasattr(self, "boton_reproducir"):
            self.boton_reproducir.cambiar_icono("reproducir")

    def _cambiar_velocidad(self, indice):
        self.velocidad = VELOCIDADES[indice]

    def _verificar(self):
        nombre = self.algoritmo.get()

        def listo(resultado):
            correctas, estables = resultado
            self.avisar(f"{nombre}: {correctas}/400 bien ordenados y {estables}/400 estables "
                        "(mismo resultado que sorted() de Python).", "ok" if correctas == estables == 400 else "error")

        self._en_segundo_plano("Verificando con 400 arreglos...", lambda avance: verificar(nombre, 400, avance), listo)

    # ===================== REPRESENTACION TEMPORAL f(x) ======================
    def _crear_pestana_temporal(self):
        cuerpo = self.pestana_temporal
        fila = self._fila_controles(cuerpo)
        medir_ahora = self._medir_temporal
        self.entrada_tamanos_temporal = fila.agregar(
            Campo(fila, self, "Tamaños de n (separados por coma)", "1000, 5000, 10000, 50000, 100000", 26, medir_ahora), expandir=True)
        self.entrada_pruebas_temporal = fila.agregar(Campo(fila, self, "Pruebas por tamaño", "3", 12, medir_ahora))
        self.combo_tipo_temporal = fila.agregar(Selector(fila, self, "Tipo de datos", list(GENERADORES_TIPO_DATOS), "Aleatorio"))
        fila.agregar(self._boton_trabajo(fila, "Medir", medir_ahora, "primario"))
        self.etiqueta_temporal = self._mensaje(cuerpo)
        self.grafica_comparaciones, self.grafica_movimientos, self.grafica_tiempo = self._fila_graficas(
            cuerpo, 3, "Pulsa Medir para ver la curva.")
        columnas = ("n", "Mejor f(n)", "Peor f(n)", "Medido", "Cuadrático: n²", "n² / Peor", "Tiempo (ms)")
        self.tabla_temporal = self._tabla_en_tarjeta(cuerpo, "Tabla de datos (igual a la de la presentación)", columnas,
                                                     (90, 110, 130, 120, 150, 120, 100), alto=5)

    def _leer_tamanos(self, texto):
        tamanos = sorted({leer_entero(v) for v in texto.split(",") if v.strip()})
        if not tamanos or tamanos[0] < 2:
            raise ValueError
        return tamanos

    def _medir_temporal(self):
        try:
            tamanos = self._leer_tamanos(self.entrada_tamanos_temporal.get())
        except ValueError:
            self._error(self.entrada_tamanos_temporal, "Escribe tamaños enteros >= 2 separados por coma.")
            return
        try:
            pruebas = leer_entero(self.entrada_pruebas_temporal.get())
            if pruebas < 1:
                raise ValueError
        except ValueError:
            self._error(self.entrada_pruebas_temporal, "Las pruebas por tamaño deben ser un entero >= 1.")
            return

        nombre = self.algoritmo.get()
        datos = ALGORITMOS[nombre]
        if datos["limite_n"] is not None:
            tamanos = [n for n in tamanos if n <= datos["limite_n"]]
            if not tamanos:
                self._error(self.entrada_tamanos_temporal, f"{nombre} solo se mide hasta n = {miles(datos['limite_n'])}.")
                return
        tipo_datos = self.combo_tipo_temporal.get()
        generador = GENERADORES_TIPO_DATOS[tipo_datos]

        def trabajo(avance):
            partes = tramos(avance, [datos["f_peor"](n) for n in tamanos])
            return [medir(nombre, n, pruebas, generador, parte) for n, parte in zip(tamanos, partes)]

        def listo(resultados):
            comparaciones = [r[0] for r in resultados]
            movimientos = [r[1] for r in resultados]
            tiempos = [r[2] for r in resultados]
            ultimo = tamanos[-1]
            self.etiqueta_temporal.config(
                text=(f"{nombre}, {tipo_datos}: con n = {miles(ultimo)} hizo {miles(comparaciones[-1])} comparaciones "
                      f"(mejor: {miles(datos['f_mejor'](ultimo))}, peor: {miles(datos['f_peor'](ultimo))}). "
                      f"Big O teórico: {datos['big_o']['Mejor']} a {datos['big_o']['Peor']}."))
            filas = []
            for n, c, t in zip(tamanos, comparaciones, tiempos):
                peor = datos["f_peor"](n)
                filas.append((miles(n), miles(datos["f_mejor"](n)), miles(peor), miles(c), miles(n * n),
                              "≈ " + miles(n * n / peor) + "x", miles(t, 1)))
            self._llenar(self.tabla_temporal, filas)
            self._graficar_temporal(tamanos, comparaciones, movimientos, tiempos)

        self._en_segundo_plano(f"Midiendo {nombre}...", trabajo, listo)

    def _graficar_temporal(self, tamanos, comparaciones, movimientos, tiempos):
        # Curvas teoricas desde 0 hasta el n mas grande, como en la diapositiva
        nombre = self.algoritmo.get()
        datos = ALGORITMOS[nombre]
        xs = [tamanos[-1] * i // 30 for i in range(31)]
        self.grafica_comparaciones.lineas(f"{nombre}: comparaciones vs n", [
            serie(f"{datos['texto_peor']} (peor caso)", xs, [datos["f_peor"](n) for n in xs], GRIS, True, datos["f_peor"]),
            serie("Medido", tamanos, comparaciones, AZUL_OSCURO),
            serie(f"{datos['texto_mejor']} (mejor caso)", xs, [datos["f_mejor"](n) for n in xs], DORADO, True, datos["f_mejor"]),
        ], eje_x="n", eje_y="Comparaciones")
        self.grafica_movimientos.lineas("Movimientos vs n", [serie("Medido", tamanos, movimientos, AZUL)],
                                        eje_x="n", eje_y="Movimientos")
        self.grafica_tiempo.lineas("Tiempo vs n", [serie("Medido", tamanos, tiempos, AZUL_CLARO, formato=milisegundos)],
                                   eje_x="n", eje_y="Tiempo (ms)")

    # ============================ RENDIMIENTO ================================
    def _crear_pestana_rendimiento(self):
        cuerpo = self.pestana_rendimiento
        fila = self._fila_controles(cuerpo)
        self.entrada_n_rendimiento = fila.agregar(Campo(fila, self, "Tamaño de la lista (n)", "100000", 14, self._comparar_casos))
        fila.agregar(self._boton_trabajo(fila, "Comparar casos", self._comparar_casos, "primario"))
        fila.agregar(Boton(fila, self, "Probar modo galope", self._probar_galope))
        self.etiqueta_rendimiento = self._mensaje(cuerpo)
        self.grafica_casos_comp, self.grafica_casos_tiempo = self._fila_graficas(
            cuerpo, 2, "Pulsa Comparar casos para medir los cuatro tipos de entrada.")
        columnas = ("Caso", "Con galope", "Sin galope (uno a uno)", "Veces menos")
        self.tabla_galope = self._tabla_en_tarjeta(cuerpo, "Modo galope: comparaciones en la fusión de dos runs de 1.000",
                                                   columnas, (420, 140, 180, 120), alto=2)

    def _comparar_casos(self):
        try:
            n = leer_entero(self.entrada_n_rendimiento.get())
            if n < 100:
                raise ValueError
        except ValueError:
            self._error(self.entrada_n_rendimiento, "El tamaño n debe ser un entero mayor o igual a 100.")
            return

        nombre = self.algoritmo.get()
        datos = ALGORITMOS[nombre]
        n = self._limitar(n)
        casos = ["Ya ordenado", "Orden inverso", "Casi ordenado (1 %)", "Aleatorio"]

        def trabajo(avance):
            partes = tramos(avance, [1] * len(casos))
            return [medir(nombre, n, 3, GENERADORES_TIPO_DATOS[caso], parte) for caso, parte in zip(casos, partes)]

        def listo(resultados):
            comparaciones = [r[0] for r in resultados]
            tiempos = [r[2] for r in resultados]
            nombres_caso = {tipo: etiqueta for etiqueta, tipo, _ in datos["casos"]}
            etiquetas = [caso.replace(" (1 %)", "") + (f"\n({nombres_caso[caso].lower()})" if caso in nombres_caso else "\n(1 %)")
                         for caso in casos]
            colores = [DORADO if nombres_caso.get(caso) == "Mejor" else
                       AZUL_CLARO if caso not in nombres_caso else AZUL_OSCURO for caso in casos]
            self.grafica_casos_comp.barras(
                f"{nombre}: comparaciones con n = {miles(n)}", etiquetas,
                [{"valores": comparaciones, "colores": colores, "textos": [miles(c) for c in comparaciones]}],
                referencias=[(datos["f_mejor"](n), DORADO, datos["texto_mejor"]), (datos["f_peor"](n), GRIS, datos["texto_peor"])])
            self.grafica_casos_tiempo.barras(
                f"Tiempo con n = {miles(n)} (mejor de 3)", etiquetas,
                [{"valores": tiempos, "colores": colores, "textos": [milisegundos(t) for t in tiempos]}], eje_y="Tiempo (ms)")
            self.etiqueta_rendimiento.config(text=(
                f"{nombre} con n = {miles(n)}: ya ordenado {miles(comparaciones[0])}, orden inverso "
                f"{miles(comparaciones[1])}, aleatorio {miles(comparaciones[3])} comparaciones. "
                f"Big O teórico: mejor {datos['big_o']['Mejor']}, promedio {datos['big_o']['Promedio']}, "
                f"peor {datos['big_o']['Peor']}."))

        self._en_segundo_plano("Midiendo los cuatro tipos de entrada...", trabajo, listo)

    def _probar_galope(self):
        metodo = self.algoritmo.get()
        if metodo == "Insertion Sort":
            self.etiqueta_rendimiento.config(text="Insertion Sort no fusiona: el modo galope solo existe en TimSort y Powersort.")
            return
        # Caso 1: dos runs de 1.000 donde uno va entero antes que el otro
        caso1 = list(range(1000, 2000)) + list(range(1000))
        # Caso 2: dos runs de 1.000 armados con bloques alternos de 200
        izquierda, derecha = [], []
        for bloque in range(10):
            (izquierda if bloque % 2 == 0 else derecha).extend(range(bloque * 200, (bloque + 1) * 200))
        caso2 = izquierda + derecha

        filas = []
        for nombre, arreglo in (("Uno de los runs va entero antes que el otro", caso1),
                                ("Bloques alternos de 200 elementos", caso2)):
            con = ordenar(metodo, list(arreglo), galope=True)["comparaciones_fusion"]
            sin = ordenar(metodo, list(arreglo), galope=False)["comparaciones_fusion"]
            filas.append((nombre, miles(con), miles(sin), f"≈ {miles(sin / con, 1)}x"))
        self._llenar(self.tabla_galope, filas)

    # ================================ DEMO ==================================
    def _crear_pestana_demo(self):
        cuerpo = self.pestana_demo
        fila = self._fila_controles(cuerpo)
        self.entrada_n_demo = fila.agregar(Campo(fila, self, "Cantidad de valores (n)", "10000", 14, self._ejecutar_demo))
        self.combo_tipo_demo = fila.agregar(Selector(fila, self, "Tipo de datos", list(GENERADORES_TIPO_DATOS), "Aleatorio"))
        fila.agregar(self._boton_trabajo(fila, "Generar y ordenar", self._ejecutar_demo, "primario"))
        fila.agregar(self._boton_trabajo(fila, "Reiniciar gráfica", self._reiniciar_demo))
        fila.agregar(self._boton_trabajo(fila, "Tabla de la presentación", self._tabla_presentacion))
        self.etiqueta_resultado_demo = self._mensaje(cuerpo, "Aún no se ha ejecutado ninguna prueba.")
        self.etiqueta_muestra_demo = Parrafo(cuerpo, text="", bg=FONDO, fg=TEXTO_SUAVE, font=self.fuente(12))
        self.etiqueta_muestra_demo.pack(fill="x", padx=self.margen)
        self.grafica_demo = self._fila_graficas(cuerpo, 1, "Cada clic en Generar y ordenar agrega un punto a la gráfica.")[0]
        columnas = ("n", "Aleatorio", "Casi ordenado", "Ordenado")
        self.tabla_demo = self._tabla_en_tarjeta(cuerpo, "Tiempos medidos (mejor de 3)", columnas, (120, 160, 160, 160), alto=5)

    def _ejecutar_demo(self):
        try:
            n = leer_entero(self.entrada_n_demo.get())
            if n < 1:
                raise ValueError
        except ValueError:
            self._error(self.entrada_n_demo, "La cantidad de valores debe ser un entero mayor o igual a 1.")
            return

        nombre = self.algoritmo.get()
        n = self._limitar(n)
        tipo_datos = self.combo_tipo_demo.get()

        def trabajo(avance):
            arreglo_original = GENERADORES_TIPO_DATOS[tipo_datos](n)
            arreglo_a_ordenar = list(arreglo_original)
            avance(0.1)
            inicio = time.perf_counter_ns()
            contador = ordenar(nombre, arreglo_a_ordenar)
            tiempo_ms = (time.perf_counter_ns() - inicio) / 1_000_000
            avance(0.9)
            correcto = "sí" if arreglo_a_ordenar == sorted(arreglo_original) else "NO"
            return arreglo_original, arreglo_a_ordenar, contador, tiempo_ms, correcto

        def listo(resultado):
            arreglo_original, arreglo_a_ordenar, contador, tiempo_ms, correcto = resultado
            self.etiqueta_resultado_demo.config(
                text=(f"{nombre}: n = {miles(n)} ({tipo_datos}) ordenados en {miles(tiempo_ms, 3)} ms con "
                      f"{miles(contador['comparaciones'])} comparaciones. Igual a sorted(): {correcto}."))
            if n <= 30:
                self.etiqueta_muestra_demo.config(text=f"Antes: {arreglo_original}\nDespués: {arreglo_a_ordenar}")
            else:
                self.etiqueta_muestra_demo.config(text=(f"Antes (primeros 15): {arreglo_original[:15]} ...\n"
                                                        f"Después (primeros 15): {arreglo_a_ordenar[:15]} ..."))
            self.puntos_demo_n.append(n)
            self.puntos_demo_tiempo.append(tiempo_ms)
            self._graficar_demo()

        self._en_segundo_plano(f"Ordenando {miles(n)} valores...", trabajo, listo)

    def _graficar_demo(self):
        puntos = sorted(zip(self.puntos_demo_n, self.puntos_demo_tiempo))
        self.grafica_demo.lineas("Puntos acumulados en esta demo (cada clic agrega un punto)",
                                 [serie("Tiempo medido", [p[0] for p in puntos], [p[1] for p in puntos], AZUL, formato=milisegundos)],
                                 eje_x="Cantidad de valores (n)", eje_y="Tiempo (ms)")

    def _reiniciar_demo(self):
        self.puntos_demo_n = []
        self.puntos_demo_tiempo = []
        self.etiqueta_resultado_demo.config(text="Aún no se ha ejecutado ninguna prueba.")
        self.etiqueta_muestra_demo.config(text="")
        self.grafica_demo.vaciar()

    def _tabla_presentacion(self):
        """Repite la medicion de la diapositiva 'Demo: tiempos medidos al variar n'."""
        nombre = self.algoritmo.get()
        tamanos = sorted({self._limite(n) for n in (1000, 5000, 10000, 50000, 100000)})
        tipos = ["Aleatorio", "Casi ordenado (1 %)", "Ya ordenado"]
        costo = ALGORITMOS[nombre]["f_peor"]

        def trabajo(avance):
            tareas = [(tipo, n) for tipo in tipos for n in tamanos]
            partes = iter(tramos(avance, [costo(n) for _, n in tareas]))
            tiempos = {tipo: [medir(nombre, n, 3, GENERADORES_TIPO_DATOS[tipo], next(partes))[2] for n in tamanos]
                       for tipo in tipos}
            arreglo = _aleatorio(100000)
            inicio = time.perf_counter_ns()
            sorted(arreglo)
            return tiempos, (time.perf_counter_ns() - inicio) / 1_000_000

        def listo(resultado):
            tiempos, tiempo_sorted = resultado
            self._llenar(self.tabla_demo, [[miles(n)] + [milisegundos(tiempos[t][i]) for t in tipos]
                                           for i, n in enumerate(tamanos)])
            self.grafica_demo.barras(
                "Tiempo (ms) según n y el tipo de datos", [miles(n) for n in tamanos],
                [{"nombre": tipo, "valores": tiempos[tipo], "colores": [color] * len(tamanos),
                  "textos": None} for tipo, color in zip(tipos, (AZUL_OSCURO, AZUL_CLARO, DORADO))],
                eje_x="n", eje_y="Tiempo (ms)")
            crece_aleatorio = tiempos["Aleatorio"][-1] / tiempos["Aleatorio"][0]
            crece_ordenado = tiempos["Ya ordenado"][-1] / tiempos["Ya ordenado"][0]
            self.etiqueta_resultado_demo.config(text=(
                f"{nombre}, de {miles(tamanos[0])} a {miles(tamanos[-1])} (x{miles(tamanos[-1] / tamanos[0])}): "
                f"aleatorio crece x{miles(crece_aleatorio, 1)} y ordenado x{miles(crece_ordenado, 1)}. "
                f"sorted() de Python (escrito en C) con 100.000 aleatorios: {miles(tiempo_sorted, 1)} ms."))
            self.etiqueta_muestra_demo.config(text="")

        self._en_segundo_plano(f"Midiendo {len(tamanos)} tamaños x 3 tipos de datos...", trabajo, listo)

    # ================================ CALIDAD ================================
    def _fila_validacion(self, padre, texto_boton, comando, explicacion, titulos):
        """Boton de validar con su explicacion y debajo los indicadores grandes."""
        px = self.px
        tarjeta = self._tarjeta(padre)
        tarjeta.pack(fill="x", padx=self.margen, pady=(px(4), px(6)))
        fila = tk.Frame(tarjeta, bg=TARJETA)
        fila.pack(fill="x", padx=px(14), pady=px(11))
        self._boton_trabajo(fila, texto_boton, comando, "primario").pack(side="left", padx=(0, px(14)))
        Parrafo(fila, text=explicacion, bg=TARJETA, fg=TEXTO_SUAVE, font=self.fuente(13), anchor="w").pack(
            side="left", fill="x", expand=True)
        etiqueta = self._mensaje(padre)
        marco = tk.Frame(padre, bg=FONDO)
        marco.pack(fill="x", padx=self.margen, pady=px(4))
        indicadores = []
        for i, titulo in enumerate(titulos):
            marco.columnconfigure(i, weight=1, uniform="indicadores")
            indicador = Indicador(marco, self, titulo)
            indicador.grid(row=0, column=i, sticky="ew", padx=(px(10) if i else 0, 0))
            indicadores.append(indicador)
        return etiqueta, indicadores

    def _crear_pestana_calidad(self):
        cuerpo = self.pestana_calidad
        self.etiqueta_calidad, self.indicadores_calidad = self._fila_validacion(
            cuerpo, "Validar calidad", self._validar_calidad,
            "Ordena 400 arreglos contra sorted(), revisa la estabilidad y estima el Big O con las comparaciones medidas.",
            ("Bien ordenados", "Estables", "Casos con el Big O esperado"))
        self.grafica_calidad_curvas, self.grafica_calidad_razon = self._fila_graficas(
            cuerpo, 2, "Pulsa Validar calidad para ver las curvas.", alto=200)
        columnas = ("Caso", "Tipo de datos", "Teórico", "Medido", "Variación", "Resultado")
        self.tabla_calidad = self._tabla_en_tarjeta(cuerpo, "Big O teórico contra Big O medido", columnas,
                                                    (130, 150, 100, 100, 100, 120), alto=3)

    def _validar_calidad(self):
        nombre = self.algoritmo.get()

        def trabajo(avance):
            verificacion, medicion = tramos(avance, [1, 3])
            correctas, estables = verificar(nombre, 400, verificacion)
            tamanos, filas = validar_calidad(nombre, medicion)
            return correctas, estables, tamanos, filas

        def listo(resultado):
            correctas, estables, tamanos, filas = resultado
            aciertos = sum(fila["estimado"] == fila["esperado"] for fila in filas)
            self._llenar(self.tabla_calidad, [
                (fila["caso"], fila["tipo"], "Θ(" + fila["esperado"] + ")", "Θ(" + fila["estimado"] + ")",
                 miles(100 * fila["variacion"], 1) + " %",
                 "Coincide" if fila["estimado"] == fila["esperado"] else "NO coincide") for fila in filas],
                ["bien" if fila["estimado"] == fila["esperado"] else "mal" for fila in filas])
            self.etiqueta_calidad.config(text=(f"{nombre}: {correctas}/400 bien ordenados, {estables}/400 estables y "
                                               f"{aciertos}/{len(filas)} casos con el Big O esperado."))
            for indicador, (valor, total) in zip(self.indicadores_calidad, ((correctas, 400), (estables, 400), (aciertos, len(filas)))):
                indicador.poner(valor, total)
            curvas, razones = [], []
            for fila, color in zip(filas, (AZUL_OSCURO, DORADO, AZUL_CLARO)):
                g = MODELOS[fila["esperado"]]
                razon = [v / g(n) for n, v in zip(tamanos, fila["valores"])]
                promedio = statistics.mean(razon)
                etiqueta = f"{fila['tipo']}: Θ({fila['esperado']})"
                curvas.append(serie(etiqueta, tamanos, fila["valores"], color))
                razones.append(serie(etiqueta, tamanos, [r / promedio for r in razon], color, formato=lambda v: miles(v, 3)))
            self.grafica_calidad_curvas.lineas(f"{nombre}: comparaciones (escala log-log)", curvas, eje_x="n", log=True)
            self.grafica_calidad_razon.lineas("Calidad del ajuste: f(n) / modelo (plano = coincide)", razones, eje_x="n",
                                              rango_y=(0.5, 1.5), referencias=[(1, GRIS, "")])

        self._en_segundo_plano(f"Validando {nombre}...", trabajo, listo)

    # ============================== PSEUDOCODIGO =============================
    def _crear_pestana_pseudocodigo(self):
        px = self.px
        cuerpo = self.pestana_pseudocodigo
        self.etiqueta_pseudocodigo, self.indicadores_pseudocodigo = self._fila_validacion(
            cuerpo, "Validar pseudocódigo", self._validar_pseudocodigo,
            "Traduce el pseudocódigo a Python, lo ejecuta en 100 arreglos y lo compara contra sorted() y contra el código real.",
            ("Bien ordenados", "Estables", "Mismas comparaciones que el código"))
        marco = tk.Frame(cuerpo, bg=FONDO)
        marco.pack(fill="both", expand=True, padx=self.margen, pady=px(4))
        marco.columnconfigure((0, 1), weight=1, uniform="textos")
        marco.rowconfigure(0, weight=1)
        self.texto_pseudocodigo = self._crear_caja(marco, "Pseudocódigo", 0)
        self.texto_python = self._crear_caja(marco, "Python generado (línea por línea)", 1)
        self._enlazar_cajas(self.texto_pseudocodigo, self.texto_python)
        self._enlazar_cajas(self.texto_python, self.texto_pseudocodigo)

    def _crear_caja(self, padre, titulo, columna):
        px = self.px
        tarjeta = self._tarjeta(padre, titulo)
        tarjeta.grid(row=0, column=columna, sticky="nsew", padx=(px(10) if columna else 0, 0))
        caja = tk.Text(tarjeta, wrap="none", font=self.fuente(13, mono=True), bg=CODIGO_FONDO, fg="white", padx=px(10), pady=px(8),
                       relief="flat", bd=0, highlightthickness=0, cursor="arrow", width=30, height=12, spacing1=px(1))
        caja.pack(fill="both", expand=True, padx=px(8), pady=(px(4), px(8)))
        caja.tag_configure("numero", foreground=CODIGO_NUMERO)
        caja.tag_configure("clave", foreground=DORADO)
        caja.tag_configure("linea", background=CODIGO_LINEA)
        return caja

    def _enlazar_cajas(self, caja, otra):
        """Al pasar el mouse por una linea se resalta la misma linea en las dos
        cajas, y el scroll de una mueve a la otra."""
        def resaltar(evento):
            linea = caja.index(f"@{evento.x},{evento.y}").split(".")[0]
            for texto in (caja, otra):
                texto.tag_remove("linea", "1.0", "end")
                texto.tag_add("linea", f"{linea}.0", f"{linea}.0 lineend +1c")

        def limpiar(_evento):
            for texto in (caja, otra):
                texto.tag_remove("linea", "1.0", "end")

        caja.bind("<Motion>", resaltar)
        caja.bind("<Leave>", limpiar)
        caja.configure(yscrollcommand=lambda primero, _ultimo: otra.yview_moveto(primero))

    def _escribir_codigo(self, caja, texto, palabras):
        caja.config(state="normal")
        caja.delete("1.0", "end")
        margen = 5                    # ancho del numero de linea
        for numero, linea in enumerate(texto.split("\n"), 1):
            caja.insert("end", f"{numero:>3}  ", "numero")
            caja.insert("end", linea + "\n")
            for hallado in re.finditer(palabras, linea):
                caja.tag_add("clave", f"{numero}.{margen + hallado.start()}", f"{numero}.{margen + hallado.end()}")
        caja.config(state="disabled")

    def _validar_pseudocodigo(self):
        nombre = self.algoritmo.get()

        def listo(resultado):
            ordenados, estables, iguales = resultado
            self.etiqueta_pseudocodigo.config(text=(f"{nombre}: el pseudocódigo ordenó bien {ordenados}/100 arreglos, "
                                                    f"{estables}/100 estables y {iguales}/100 con exactamente las mismas "
                                                    "comparaciones que el código real."))
            for indicador, valor in zip(self.indicadores_pseudocodigo, resultado):
                indicador.poner(valor, 100)

        self._en_segundo_plano("Ejecutando el pseudocódigo...", lambda avance: validar_pseudocodigo(nombre, 100, avance), listo)

    # =============================== COMPARACION ==============================
    def _crear_pestana_comparacion(self):
        cuerpo = self.pestana_comparacion
        fila = self._fila_controles(cuerpo)
        self.entrada_tamanos_comparacion = fila.agregar(
            Campo(fila, self, "Tamaños de n (separados por coma)", "1000, 2000, 5000, 10000, 50000, 100000", 30, self._comparar_metodos),
            expandir=True)
        self.combo_tipo_comparacion = fila.agregar(Selector(fila, self, "Tipo de datos", list(GENERADORES_TIPO_DATOS), "Aleatorio"))
        fila.agregar(self._boton_trabajo(fila, "Comparar los tres", self._comparar_metodos, "primario"))
        self.etiqueta_comparacion = self._mensaje(cuerpo, "Insertion Sort solo se mide hasta n = 10.000 (más arriba tarda minutos).")
        self.grafica_comp_metodos, self.grafica_tiempo_metodos = self._fila_graficas(
            cuerpo, 2, "Pulsa Comparar los tres para ver las curvas.", alto=210)

        columnas = ("Método", "Rol", "Mejor", "Promedio", "Peor", "Espacio", "Estable", "Adaptativo")
        tabla_big_o = self._tabla_en_tarjeta(cuerpo, "Big O teórico", columnas, (130, 80, 90, 100, 100, 80, 70, 80), alto=3)
        self._llenar(tabla_big_o, [(nombre, datos["rol"], *datos["big_o"].values(), datos["estable"], datos["adaptativo"])
                                   for nombre, datos in ALGORITMOS.items()])
        columnas = ("n", *[f"{m}: comp." for m in ALGORITMOS], *[f"{m}: ms" for m in ALGORITMOS])
        self.tabla_comparacion = self._tabla_en_tarjeta(cuerpo, "Comparaciones y tiempo medidos (mejor de 2)", columnas,
                                                        (80, 130, 130, 130, 120, 120, 120), alto=6)

    def _comparar_metodos(self):
        try:
            tamanos = self._leer_tamanos(self.entrada_tamanos_comparacion.get())
        except ValueError:
            self._error(self.entrada_tamanos_comparacion, "Escribe tamaños enteros >= 2 separados por coma.")
            return

        tipo_datos = self.combo_tipo_comparacion.get()
        generador = GENERADORES_TIPO_DATOS[tipo_datos]

        def trabajo(avance):
            tareas = [(nombre, n) for nombre, datos in ALGORITMOS.items() for n in tamanos
                      if datos["limite_n"] is None or n <= datos["limite_n"]]
            partes = tramos(avance, [ALGORITMOS[nombre]["f_peor"](n) for nombre, n in tareas])
            resultados = {nombre: {} for nombre in ALGORITMOS}
            for (nombre, n), parte in zip(tareas, partes):
                resultados[nombre][n] = medir(nombre, n, 2, generador, parte)
            return resultados

        def listo(resultados):
            filas = []
            for n in tamanos:
                fila = [miles(n)]
                fila += [miles(resultados[m][n][0]) if n in resultados[m] else "-" for m in ALGORITMOS]
                fila += [miles(resultados[m][n][2], 1) if n in resultados[m] else "-" for m in ALGORITMOS]
                filas.append(fila)
            self._llenar(self.tabla_comparacion, filas)

            comparaciones, tiempos = [], []
            for nombre, medidas in resultados.items():
                if medidas:
                    ns = sorted(medidas)
                    comparaciones.append(serie(nombre, ns, [medidas[n][0] for n in ns], COLOR_METODO[nombre]))
                    tiempos.append(serie(nombre, ns, [medidas[n][2] for n in ns], COLOR_METODO[nombre], formato=milisegundos))
            self.grafica_comp_metodos.lineas("Comparaciones vs n (log-log)", comparaciones, eje_x="n", log=True)
            self.grafica_tiempo_metodos.lineas("Tiempo en ms vs n (log-log)", tiempos, eje_x="n", log=True)

            ultimo = tamanos[-1]
            tim, power = resultados["TimSort"][ultimo][0], resultados["Powersort"][ultimo][0]
            self.etiqueta_comparacion.config(text=(
                f"{tipo_datos}, n = {miles(ultimo)}: Powersort hizo "
                f"{miles(abs(tim - power) / tim * 100, 1)} % {'menos' if power <= tim else 'más'} comparaciones que TimSort. "
                "Insertion Sort solo se mide hasta n = 10.000."))

        self._en_segundo_plano("Midiendo los tres métodos...", trabajo, listo)


def main():
    if "--prueba" in sys.argv:
        correr_pruebas()
        return
    if sys.platform == "darwin" and tk.TkVersion < 8.6:
        sys.exit(MENSAJE_TK_VIEJO.format(version=tk.TkVersion))
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)      # texto nitido en pantallas escaladas
        except (ImportError, AttributeError, OSError):
            pass
    try:
        app = AplicacionOrdenamiento()
    except tk.TclError as error:
        sys.exit(f"No se pudo abrir la ventana: {error}")
    app.mainloop()


if __name__ == "__main__":
    main()
