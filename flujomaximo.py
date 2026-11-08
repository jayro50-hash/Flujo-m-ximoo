
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
from tkinter import scrolledtext
import math
import os
import random
from collections import deque
from datetime import datetime

import networkx as nx
import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.lines import Line2D


NODOS_MINIMOS = 7
NODOS_MAXIMOS = 16
CAPACIDAD_MINIMA = 1
CAPACIDAD_MAXIMA = 20
PROBABILIDAD_ARISTA_EXTRA = 0.3


NOMBRE_UNIVERSIDAD_LINEA_1 = "UPC"
NOMBRE_UNIVERSIDAD_LINEA_2 = "Universidad Peruana de Ciencias Aplicadas"
NOMBRES_INTEGRANTES = [
    "Jayro Sebastian Gabira Zuñiga",
    "Diego Edson Alvarez Leandro",
    "Elehazar Nicolas Muñoz Perales",
    "Mathias Tiziano Huiza Vilca",
]

COLOR_FONDO_OSCURO = "#16233c"
COLOR_ACENTO = "#f4a300"
COLOR_TEXTO_CLARO = "#ffffff"
COLOR_TEXTO_SECUNDARIO = "#9fb0c3"
COLOR_FONDO_CLARO = "#f0f0f0"

COLOR_ARISTA_NORMAL = "black"
COLOR_ARISTA_SIN_FLUJO = "#a6a6a6"
COLOR_ARISTA_PARCIAL = "#1f77b4"
COLOR_ARISTA_AGOTADA = "#ff8c00"
COLOR_ARISTA_CAMINO_ACTUAL = "#8e24aa"
COLOR_ARISTA_CORTE = "#d62728"
COLOR_NODO_ALCANZABLE = "#a8d5a2"
PALETA_CAMINOS = [
    "#e6194b", "#3cb44b", "#4363d8", "#f58231", "#911eb4",
    "#008080", "#9a6324", "#800000", "#808000", "#000075",
]

RADIO_CURVA_CORTA = 0.05
CANDIDATOS_RADIO_LARGA = [0.25, -0.25, 0.45, -0.45, 0.7, -0.7]
DISTANCIA_LIBRE_NODOS = 0.9
DISTANCIA_ARISTA_LARGA = 3.0

SEPARACION_HORIZONTAL = 2.6
SEPARACION_VERTICAL_MINIMA = 1.9
SEPARACION_VERTICAL_MAXIMA = 3.4
PROPORCION_PANTALLA = 1.7
MARGEN_GRAFICO = 1.0

NOMBRE_BASE_REPORTE = "Resultado_Flujo_Maximo"

class GrafoFlujo:

    def __init__(self, cantidad_nodos):
        self.cantidad_nodos = cantidad_nodos
        self.nombres_nodos = []
        indice = 0
        while indice < cantidad_nodos:
            self.nombres_nodos.append("N" + str(indice))
            indice = indice + 1

        self.capacidades = {}
        self.flujos = {}

    def agregar_nodo_ficticio(self, nombre):
        if nombre not in self.nombres_nodos:
            self.nombres_nodos.append(nombre)

    def existe_arista(self, origen, destino):
        clave = (origen, destino)
        if clave in self.capacidades:
            return True
        else:
            return False

    def obtener_nodos_en_uso(self):
        nodos_en_uso = []
        for nombre in self.nombres_nodos:
            esta_en_uso = False
            for clave in self.capacidades.keys():
                if clave[0] == nombre or clave[1] == nombre:
                    esta_en_uso = True
            if esta_en_uso:
                nodos_en_uso.append(nombre)
        return nodos_en_uso

    def esta_agotada(self, clave):
        if self.flujos[clave] == self.capacidades[clave]:
            return True
        else:
            return False

    def obtener_aristas_agotadas(self):
        aristas_agotadas = []
        for clave in self.capacidades.keys():
            if self.esta_agotada(clave):
                aristas_agotadas.append(clave)
        return aristas_agotadas

    def agregar_arista(self, origen, destino, capacidad):
        clave = (origen, destino)
        self.capacidades[clave] = capacidad
        self.flujos[clave] = 0

    def eliminar_arista(self, origen, destino):
        clave = (origen, destino)
        if clave in self.capacidades:
            del self.capacidades[clave]
        if clave in self.flujos:
            del self.flujos[clave]

    def obtener_vecinos_salientes(self, nodo):
        vecinos = []
        for clave in self.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            if origen == nodo:
                vecinos.append(destino)
        return vecinos

    def tiene_ciclo(self):
        estado = {}
        for nodo in self.nombres_nodos:
            estado[nodo] = 0 

        for nodo in self.nombres_nodos:
            if estado[nodo] == 0:
                hay_ciclo = self._dfs_deteccion_ciclo(nodo, estado)
                if hay_ciclo:
                    return True
        return False

    def _dfs_deteccion_ciclo(self, nodo_actual, estado):
        estado[nodo_actual] = 1
        vecinos = self.obtener_vecinos_salientes(nodo_actual)

        for vecino in vecinos:
            if estado[vecino] == 1:
                return True
            elif estado[vecino] == 0:
                hay_ciclo = self._dfs_deteccion_ciclo(vecino, estado)
                if hay_ciclo:
                    return True

        estado[nodo_actual] = 2
        return False

    def obtener_capacidad_residual(self, origen, destino):
        clave_directa = (origen, destino)
        clave_inversa = (destino, origen)

        if clave_directa in self.capacidades:
            capacidad_original = self.capacidades[clave_directa]
            flujo_actual = self.flujos[clave_directa]
            return capacidad_original - flujo_actual
        elif clave_inversa in self.capacidades:
            flujo_actual = self.flujos[clave_inversa]
            return flujo_actual
        else:
            return 0

    def obtener_vecinos_residuales(self, nodo):
        vecinos = set()
        for clave in self.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            if origen == nodo:
                vecinos.add(destino)
            if destino == nodo:
                vecinos.add(origen)
        return vecinos

    def actualizar_flujo_en_camino(self, camino, cantidad):
        indice = 0
        while indice < len(camino) - 1:
            origen = camino[indice]
            destino = camino[indice + 1]
            clave_directa = (origen, destino)
            clave_inversa = (destino, origen)

            if clave_directa in self.capacidades:
                self.flujos[clave_directa] = self.flujos[clave_directa] + cantidad
            elif clave_inversa in self.capacidades:
                self.flujos[clave_inversa] = self.flujos[clave_inversa] - cantidad

            indice = indice + 1

class FordFulkerson:

    def __init__(self, grafo, fuente, sumidero):
        self.grafo = grafo
        self.fuente = fuente
        self.sumidero = sumidero
        self.flujo_total = 0
        self.historial_caminos = []
        self.terminado = False

    def buscar_camino_aumento(self):
        padres = {}
        visitados = set()
        visitados.add(self.fuente)

        cola = deque()
        cola.append(self.fuente)

        while len(cola) > 0:
            nodo_actual = cola.popleft()

            if nodo_actual == self.sumidero:
                break

            vecinos = self.grafo.obtener_vecinos_residuales(nodo_actual)
            for vecino in vecinos:
                if vecino not in visitados:
                    capacidad_residual = self.grafo.obtener_capacidad_residual(nodo_actual, vecino)
                    if capacidad_residual > 0:
                        visitados.add(vecino)
                        padres[vecino] = nodo_actual
                        cola.append(vecino)

        if self.sumidero not in visitados:
            return None

        camino = [self.sumidero]
        nodo_actual = self.sumidero
        while nodo_actual != self.fuente:
            nodo_actual = padres[nodo_actual]
            camino.append(nodo_actual)
        camino.reverse()
        return camino

    def calcular_capacidad_minima(self, camino):
        capacidad_minima = None
        indice = 0
        while indice < len(camino) - 1:
            origen = camino[indice]
            destino = camino[indice + 1]
            capacidad_residual = self.grafo.obtener_capacidad_residual(origen, destino)
            if capacidad_minima is None:
                capacidad_minima = capacidad_residual
            elif capacidad_residual < capacidad_minima:
                capacidad_minima = capacidad_residual
            indice = indice + 1
        return capacidad_minima

    def ejecutar_un_paso(self):
        if self.terminado:
            return None

        camino = self.buscar_camino_aumento()
        if camino is None:
            self.terminado = True
            return None

        capacidad_minima = self.calcular_capacidad_minima(camino)
        self.grafo.actualizar_flujo_en_camino(camino, capacidad_minima)
        self.flujo_total = self.flujo_total + capacidad_minima

        informacion_paso = {}
        informacion_paso["camino"] = camino
        informacion_paso["capacidad"] = capacidad_minima
        informacion_paso["flujo_acumulado"] = self.flujo_total
        informacion_paso["agotadas"] = self.obtener_aristas_agotadas_en_camino(camino)
        self.historial_caminos.append(informacion_paso)

        return informacion_paso

    def obtener_aristas_de_camino(self, camino):
        aristas = []
        indice = 0
        while indice < len(camino) - 1:
            origen = camino[indice]
            destino = camino[indice + 1]
            if (origen, destino) in self.grafo.capacidades:
                aristas.append((origen, destino))
            elif (destino, origen) in self.grafo.capacidades:
                aristas.append((destino, origen))
            indice = indice + 1
        return aristas

    def obtener_aristas_agotadas_en_camino(self, camino):
        aristas_agotadas = []
        for arista in self.obtener_aristas_de_camino(camino):
            if self.grafo.esta_agotada(arista):
                aristas_agotadas.append(arista)
        return aristas_agotadas

    def obtener_aristas_ultimo_camino(self):
        if len(self.historial_caminos) == 0:
            return []
        ultimo_paso = self.historial_caminos[len(self.historial_caminos) - 1]
        return self.obtener_aristas_de_camino(ultimo_paso["camino"])

    def obtener_camino_por_arista(self):
        camino_por_arista = {}
        numero_camino = 1
        for paso in self.historial_caminos:
            for arista in self.obtener_aristas_de_camino(paso["camino"]):
                camino_por_arista[arista] = numero_camino
            numero_camino = numero_camino + 1
        return camino_por_arista

    def calcular_corte_minimo(self):
        visitados = set()
        visitados.add(self.fuente)

        cola = deque()
        cola.append(self.fuente)

        while len(cola) > 0:
            nodo_actual = cola.popleft()
            vecinos = self.grafo.obtener_vecinos_residuales(nodo_actual)
            for vecino in vecinos:
                if vecino not in visitados:
                    capacidad_residual = self.grafo.obtener_capacidad_residual(nodo_actual, vecino)
                    if capacidad_residual > 0:
                        visitados.add(vecino)
                        cola.append(vecino)

        aristas_corte = []
        for clave in self.grafo.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            if origen in visitados and destino not in visitados:
                aristas_corte.append(clave)

        return aristas_corte, visitados

class AplicacionFlujoMaximo(tk.Tk):

    def __init__(self):
        super().__init__()
        self.title("Problema del Flujo Maximo - Algoritmo de Ford-Fulkerson")
        self.geometry("1150x760")

        self.cantidad_nodos = 0
        self.grafo = None
        self.modo_construccion = tk.StringVar(value="manual")
        self.solucionador = None
        self.fuentes_seleccionadas = []
        self.sumideros_seleccionados = []
        self.nodo_fuente_final = None
        self.nodo_sumidero_final = None
        self.posiciones_layout = None
        self.respaldo_capacidades = None
        self.respaldo_flujos = None
        self.respaldo_nombres_nodos = None
        self.nodos_seleccion = []
        self.marco_principal_ejecucion = None
        self.radios_aristas = {}
        self.reporte_guardado = False
        self.ruta_reporte = ""
        self.modo_vista_resultado = "estado"
        self.marco_grafo_resultado = None
        self.boton_vista_resultado = None

        self.contenedor = tk.Frame(self)
        self.contenedor.pack(fill="both", expand=True)

        self.mostrar_pantalla_bienvenida()
        
    def limpiar_contenedor(self):
        lista_hijos = self.contenedor.winfo_children()
        for hijo in lista_hijos:
            hijo.destroy()

    def crear_boton_atras(self, marco_padre, comando):
        boton_atras = tk.Button(
            marco_padre, text="\u2190 Atras", command=comando,
            font=("Arial", 9, "bold"), relief="flat",
            bg="#e0e0e0", fg="#333333", padx=10, pady=4, cursor="hand2"
        )
        boton_atras.place(x=15, y=15)
        return boton_atras

    def mostrar_pantalla_bienvenida(self):
        self.limpiar_contenedor()
        self.contenedor.configure(bg=COLOR_FONDO_OSCURO)

        etiqueta_superior = tk.Label(
            self.contenedor, text="SIMULADOR DE", font=("Arial", 13, "bold"),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_SECUNDARIO
        )
        etiqueta_superior.pack(pady=(50, 0))

        etiqueta_titulo = tk.Label(
            self.contenedor, text="FORD-FULKERSON", font=("Arial", 34, "bold"),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_ACENTO
        )
        etiqueta_titulo.pack(pady=(0, 8))

        etiqueta_subtitulo = tk.Label(
            self.contenedor, text="Algoritmo de Flujo Maximo en Grafos Dirigidos",
            font=("Arial", 12), bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_CLARO
        )
        etiqueta_subtitulo.pack(pady=(0, 25))

        marco_descripcion = tk.Frame(
            self.contenedor, bg=COLOR_FONDO_OSCURO,
            highlightbackground=COLOR_ACENTO, highlightthickness=2
        )
        marco_descripcion.pack(padx=140, fill="x")

        texto_descripcion = (
            "Ford-Fulkerson calcula cuanto se puede enviar, como maximo, desde un punto A "
            "hasta un punto B a traves de una red con capacidades limitadas como tuberias "
            "o carreteras. Encuentra rutas libres una por una y envia por cada una lo que "
            "el tramo mas angosto le permita, hasta que ya no queda ninguna ruta disponible. "
            "Ahi esta el flujo maximo."
        )
        etiqueta_descripcion = tk.Label(
            marco_descripcion, text=texto_descripcion, font=("Arial", 11),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_CLARO, justify="left",
            padx=20, pady=18, wraplength=780
        )
        etiqueta_descripcion.pack()

        boton_comenzar = tk.Button(
            self.contenedor, text="\u25B6  Comenzar Simulacion", font=("Arial", 12, "bold"),
            bg=COLOR_ACENTO, fg=COLOR_FONDO_OSCURO, activebackground="#ffb733",
            relief="flat", padx=18, pady=9, cursor="hand2",
            command=self.mostrar_pantalla_configuracion
        )
        boton_comenzar.pack(pady=28)

        marco_integrantes = tk.Frame(
            self.contenedor, bg=COLOR_FONDO_OSCURO,
            highlightbackground=COLOR_ACENTO, highlightthickness=2
        )
        marco_integrantes.pack(pady=5)

        etiqueta_titulo_integrantes = tk.Label(
            marco_integrantes, text="INTEGRANTES DEL GRUPO 4:", font=("Arial", 11, "bold"),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_CLARO
        )
        etiqueta_titulo_integrantes.pack(pady=(16, 10), padx=50)

        for nombre_integrante in NOMBRES_INTEGRANTES:
            etiqueta_nombre = tk.Label(
                marco_integrantes, text="\u2022 " + nombre_integrante, font=("Arial", 10),
                bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_SECUNDARIO
            )
            etiqueta_nombre.pack(pady=3, padx=50)

        espaciador_final = tk.Label(marco_integrantes, text="", bg=COLOR_FONDO_OSCURO)
        espaciador_final.pack(pady=6)

        marco_pie = tk.Frame(self.contenedor, bg=COLOR_FONDO_OSCURO)
        marco_pie.pack(side="bottom", anchor="w", padx=25, pady=20)

        etiqueta_universidad_1 = tk.Label(
            marco_pie, text=NOMBRE_UNIVERSIDAD_LINEA_1, font=("Arial", 13, "bold"),
            bg=COLOR_FONDO_OSCURO, fg="#e2453c"
        )
        etiqueta_universidad_1.pack(anchor="w")

        etiqueta_universidad_2 = tk.Label(
            marco_pie, text=NOMBRE_UNIVERSIDAD_LINEA_2, font=("Arial", 9),
            bg=COLOR_FONDO_OSCURO, fg=COLOR_TEXTO_SECUNDARIO
        )
        etiqueta_universidad_2.pack(anchor="w")

    def mostrar_pantalla_configuracion(self):
        self.limpiar_contenedor()
        self.contenedor.configure(bg=COLOR_FONDO_CLARO)

        self.crear_boton_atras(self.contenedor, self.mostrar_pantalla_bienvenida)

        titulo = tk.Label(self.contenedor, text="Configuracion del Grafo", font=("Arial", 16, "bold"))
        titulo.pack(pady=15)

        marco_nodos = tk.Frame(self.contenedor)
        marco_nodos.pack(pady=10)

        etiqueta_nodos = tk.Label(marco_nodos, text="Cantidad de nodos (entre 7 y 16):")
        etiqueta_nodos.pack(side="left", padx=5)

        self.entrada_nodos = tk.Entry(marco_nodos, width=6)
        self.entrada_nodos.pack(side="left", padx=5)
        if self.cantidad_nodos > 0:
            self.entrada_nodos.insert(0, str(self.cantidad_nodos))

        marco_modo = tk.Frame(self.contenedor)
        marco_modo.pack(pady=10)

        etiqueta_modo = tk.Label(marco_modo, text="Modo de construccion del grafo:")
        etiqueta_modo.pack(anchor="w")

        opcion_manual = tk.Radiobutton(marco_modo, text="Manual", variable=self.modo_construccion, value="manual")
        opcion_manual.pack(anchor="w")

        opcion_aleatorio = tk.Radiobutton(marco_modo, text="Aleatorio", variable=self.modo_construccion, value="aleatorio")
        opcion_aleatorio.pack(anchor="w")

        boton_continuar = tk.Button(self.contenedor, text="Continuar", command=self.procesar_configuracion_inicial, font=("Arial", 11, "bold"))
        boton_continuar.pack(pady=20)

    def procesar_configuracion_inicial(self):
        texto_nodos = self.entrada_nodos.get().strip()

        if texto_nodos.isdigit() == False:
            messagebox.showerror("Error", "Debe ingresar un numero entero valido.")
            return

        cantidad = int(texto_nodos)
        if cantidad < NODOS_MINIMOS or cantidad > NODOS_MAXIMOS:
            messagebox.showerror("Error", "La cantidad de nodos debe estar entre 7 y 16.")
            return

        self.cantidad_nodos = cantidad
        self.grafo = GrafoFlujo(cantidad)
        self.fuentes_seleccionadas = []
        self.sumideros_seleccionados = []

        modo = self.modo_construccion.get()
        if modo == "manual":
            self.mostrar_pantalla_manual()
        else:
            self.generar_grafo_aleatorio()
            self.mostrar_pantalla_seleccion()

    def determinar_cantidad_de_niveles(self):
        minimo_niveles = 4
        maximo_niveles = 6
        if maximo_niveles > self.cantidad_nodos - 1:
            maximo_niveles = self.cantidad_nodos - 1
        if minimo_niveles > maximo_niveles:
            minimo_niveles = maximo_niveles
        return random.randint(minimo_niveles, maximo_niveles)

    def repartir_nodos_en_niveles(self, cantidad_niveles):
        tamanos_de_niveles = []
        indice = 0
        while indice < cantidad_niveles:
            tamanos_de_niveles.append(1)
            indice = indice + 1

        nodos_restantes = self.cantidad_nodos - cantidad_niveles
        while nodos_restantes > 0:
            if cantidad_niveles > 2:
                indice_nivel_elegido = random.randint(1, cantidad_niveles - 2)
            else:
                indice_nivel_elegido = 0
            tamanos_de_niveles[indice_nivel_elegido] = tamanos_de_niveles[indice_nivel_elegido] + 1
            nodos_restantes = nodos_restantes - 1

        return tamanos_de_niveles

    def generar_grafo_aleatorio(self):
        cantidad_niveles = self.determinar_cantidad_de_niveles()
        tamanos_de_niveles = self.repartir_nodos_en_niveles(cantidad_niveles)

        nombres_disponibles = list(self.grafo.nombres_nodos)
        random.shuffle(nombres_disponibles)

        niveles_de_nombres = []
        indice_actual = 0
        for tamano in tamanos_de_niveles:
            grupo_de_nombres = nombres_disponibles[indice_actual: indice_actual + tamano]
            niveles_de_nombres.append(grupo_de_nombres)
            indice_actual = indice_actual + tamano

        indice_nivel = 0
        while indice_nivel < len(niveles_de_nombres) - 1:
            nivel_actual = niveles_de_nombres[indice_nivel]
            nivel_siguiente = niveles_de_nombres[indice_nivel + 1]
            for nodo_origen in nivel_actual:
                nodo_destino = random.choice(nivel_siguiente)
                capacidad = random.randint(CAPACIDAD_MINIMA, CAPACIDAD_MAXIMA)
                self.grafo.agregar_arista(nodo_origen, nodo_destino, capacidad)
            indice_nivel = indice_nivel + 1

        indice_nivel = 1
        while indice_nivel < len(niveles_de_nombres):
            nivel_actual = niveles_de_nombres[indice_nivel]
            nivel_anterior = niveles_de_nombres[indice_nivel - 1]
            for nodo_destino in nivel_actual:
                ya_tiene_entrada = False
                for nodo_origen_posible in nivel_anterior:
                    if self.grafo.existe_arista(nodo_origen_posible, nodo_destino):
                        ya_tiene_entrada = True
                if ya_tiene_entrada == False:
                    nodo_origen = random.choice(nivel_anterior)
                    capacidad = random.randint(CAPACIDAD_MINIMA, CAPACIDAD_MAXIMA)
                    self.grafo.agregar_arista(nodo_origen, nodo_destino, capacidad)
            indice_nivel = indice_nivel + 1

        indice_nivel_origen = 0
        while indice_nivel_origen < len(niveles_de_nombres):
            indice_nivel_destino = indice_nivel_origen + 1
            while indice_nivel_destino < len(niveles_de_nombres):
                for nodo_origen in niveles_de_nombres[indice_nivel_origen]:
                    for nodo_destino in niveles_de_nombres[indice_nivel_destino]:
                        probabilidad = random.random()
                        if probabilidad < PROBABILIDAD_ARISTA_EXTRA:
                            if self.grafo.existe_arista(nodo_origen, nodo_destino) == False:
                                capacidad = random.randint(CAPACIDAD_MINIMA, CAPACIDAD_MAXIMA)
                                self.grafo.agregar_arista(nodo_origen, nodo_destino, capacidad)
                indice_nivel_destino = indice_nivel_destino + 1
            indice_nivel_origen = indice_nivel_origen + 1

    def mostrar_pantalla_manual(self):
        self.limpiar_contenedor()
        self.contenedor.configure(bg=COLOR_FONDO_CLARO)

        self.crear_boton_atras(self.contenedor, self.mostrar_pantalla_configuracion)

        titulo = tk.Label(self.contenedor, text="Construccion Manual del Grafo", font=("Arial", 16, "bold"))
        titulo.pack(pady=10)

        marco_formulario = tk.Frame(self.contenedor)
        marco_formulario.pack(pady=10)

        etiqueta_origen = tk.Label(marco_formulario, text="Nodo origen:")
        etiqueta_origen.grid(row=0, column=0, padx=5, pady=5)

        self.combo_origen = ttk.Combobox(marco_formulario, values=self.grafo.nombres_nodos, width=8, state="readonly")
        self.combo_origen.grid(row=0, column=1, padx=5, pady=5)

        etiqueta_destino = tk.Label(marco_formulario, text="Nodo destino:")
        etiqueta_destino.grid(row=0, column=2, padx=5, pady=5)

        self.combo_destino = ttk.Combobox(marco_formulario, values=self.grafo.nombres_nodos, width=8, state="readonly")
        self.combo_destino.grid(row=0, column=3, padx=5, pady=5)

        etiqueta_capacidad = tk.Label(marco_formulario, text="Capacidad:")
        etiqueta_capacidad.grid(row=0, column=4, padx=5, pady=5)

        self.entrada_capacidad = tk.Entry(marco_formulario, width=8)
        self.entrada_capacidad.grid(row=0, column=5, padx=5, pady=5)

        boton_agregar = tk.Button(marco_formulario, text="Agregar arista", command=self.agregar_arista_manual)
        boton_agregar.grid(row=0, column=6, padx=10, pady=5)

        etiqueta_lista = tk.Label(self.contenedor, text="Aristas agregadas:")
        etiqueta_lista.pack(pady=(10, 0))

        self.lista_aristas = tk.Listbox(self.contenedor, width=60, height=12)
        self.lista_aristas.pack(pady=10)

        for clave in self.grafo.capacidades.keys():
            origen_existente = clave[0]
            destino_existente = clave[1]
            capacidad_existente = self.grafo.capacidades[clave]
            texto_existente = origen_existente + " -> " + destino_existente + "   (capacidad = " + str(capacidad_existente) + ")"
            self.lista_aristas.insert("end", texto_existente)

        marco_botones = tk.Frame(self.contenedor)
        marco_botones.pack(pady=10)

        boton_eliminar = tk.Button(marco_botones, text="Eliminar seleccionada", command=self.eliminar_arista_manual)
        boton_eliminar.pack(side="left", padx=10)

        boton_finalizar = tk.Button(marco_botones, text="Finalizar Grafo", command=self.finalizar_grafo_manual, font=("Arial", 11, "bold"))
        boton_finalizar.pack(side="left", padx=10)

    def validar_datos_arista(self, origen, destino, texto_capacidad):
        if origen == "" or destino == "":
            return "Debe seleccionar el nodo origen y el nodo destino."

        if origen == destino:
            return "El nodo origen y el nodo destino no pueden ser iguales."

        if texto_capacidad.isdecimal() == False:
            return "La capacidad debe ser un numero entero positivo."

        if int(texto_capacidad) <= 0:
            return "La capacidad debe ser mayor a cero."

        if self.grafo.existe_arista(origen, destino):
            return "Esa arista ya fue agregada."

        return ""

    def agregar_arista_manual(self):
        origen = self.combo_origen.get()
        destino = self.combo_destino.get()
        texto_capacidad = self.entrada_capacidad.get().strip()

        mensaje_error = self.validar_datos_arista(origen, destino, texto_capacidad)
        if mensaje_error != "":
            messagebox.showerror("Error", mensaje_error)
            return

        capacidad = int(texto_capacidad)
        self.grafo.agregar_arista(origen, destino, capacidad)
        texto_mostrado = origen + " -> " + destino + "   (capacidad = " + str(capacidad) + ")"
        self.lista_aristas.insert("end", texto_mostrado)

    def eliminar_arista_manual(self):
        seleccion = self.lista_aristas.curselection()
        if len(seleccion) == 0:
            messagebox.showerror("Error", "Debe seleccionar una arista de la lista para eliminarla.")
            return

        indice = seleccion[0]
        texto = self.lista_aristas.get(indice)
        primera_parte = texto.split(" -> ")
        origen = primera_parte[0]
        segunda_parte = primera_parte[1]
        destino = segunda_parte.split("   (")[0]

        self.grafo.eliminar_arista(origen, destino)
        self.lista_aristas.delete(indice)

    def finalizar_grafo_manual(self):
        if len(self.grafo.capacidades) == 0:
            messagebox.showerror("Error", "Debe agregar al menos una arista antes de continuar.")
            return

        if self.grafo.tiene_ciclo():
            messagebox.showerror(
                "Ciclo detectado",
                "El grafo ingresado contiene al menos un ciclo.\n\n"
                "El algoritmo de Ford-Fulkerson requiere que la red de flujo "
                "no contenga ciclos entre las aristas ingresadas.\n\n"
                "Por favor elimine o corrija la arista responsable e intente nuevamente."
            )
            return

        self.mostrar_pantalla_seleccion()

    def construir_grafo_networkx(self):
        grafo_dibujo = nx.DiGraph()
        for nombre in self.grafo.obtener_nodos_en_uso():
            grafo_dibujo.add_node(nombre)
        for clave in self.grafo.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            grafo_dibujo.add_edge(origen, destino)
        return grafo_dibujo

    def calcular_niveles_topologicos(self, grafo_dibujo):

        grados_entrada = {}
        for nodo in grafo_dibujo.nodes():
            grados_entrada[nodo] = 0
        for arista in grafo_dibujo.edges():
            destino = arista[1]
            grados_entrada[destino] = grados_entrada[destino] + 1

        nivel_de_nodo = {}
        cola = deque()
        for nodo in grafo_dibujo.nodes():
            if grados_entrada[nodo] == 0:
                nivel_de_nodo[nodo] = 0
                cola.append(nodo)

        grados_entrada_restante = dict(grados_entrada)
        while len(cola) > 0:
            nodo_actual = cola.popleft()
            vecinos = list(grafo_dibujo.successors(nodo_actual))
            for vecino in vecinos:
                nivel_propuesto = nivel_de_nodo[nodo_actual] + 1
                if vecino not in nivel_de_nodo:
                    nivel_de_nodo[vecino] = nivel_propuesto
                elif nivel_propuesto > nivel_de_nodo[vecino]:
                    nivel_de_nodo[vecino] = nivel_propuesto

                grados_entrada_restante[vecino] = grados_entrada_restante[vecino] - 1
                if grados_entrada_restante[vecino] == 0:
                    cola.append(vecino)

        for nodo in grafo_dibujo.nodes():
            if nodo not in nivel_de_nodo:
                nivel_de_nodo[nodo] = 0

        return nivel_de_nodo

    def construir_posiciones_por_niveles(self, grafo_dibujo, nivel_de_nodo):
        nodos_por_nivel = {}
        for nodo in grafo_dibujo.nodes():
            nivel = nivel_de_nodo[nodo]
            if nivel not in nodos_por_nivel:
                nodos_por_nivel[nivel] = []
            nodos_por_nivel[nivel].append(nodo)

        posiciones = {}
        separacion_vertical = self.calcular_separacion_vertical(nodos_por_nivel)
        niveles_ordenados = sorted(nodos_por_nivel.keys())
        for nivel in niveles_ordenados:
            nodos_en_nivel = nodos_por_nivel[nivel]
            cantidad_en_nivel = len(nodos_en_nivel)
            indice = 0
            while indice < cantidad_en_nivel:
                nodo = nodos_en_nivel[indice]
                coordenada_x = nivel * SEPARACION_HORIZONTAL
                coordenada_y = (indice - (cantidad_en_nivel - 1) / 2.0) * separacion_vertical
                posiciones[nodo] = (coordenada_x, coordenada_y)
                indice = indice + 1

        return posiciones

    def calcular_separacion_vertical(self, nodos_por_nivel):
        filas_maximas = 1
        for nivel in nodos_por_nivel.keys():
            if len(nodos_por_nivel[nivel]) > filas_maximas:
                filas_maximas = len(nodos_por_nivel[nivel])

        if filas_maximas == 1:
            return SEPARACION_VERTICAL_MINIMA

        ultimo_nivel = max(nodos_por_nivel.keys())
        ancho_total = SEPARACION_HORIZONTAL * ultimo_nivel
        alto_deseado = ancho_total / PROPORCION_PANTALLA
        separacion = alto_deseado / (filas_maximas - 1)

        if separacion < SEPARACION_VERTICAL_MINIMA:
            separacion = SEPARACION_VERTICAL_MINIMA
        if separacion > SEPARACION_VERTICAL_MAXIMA:
            separacion = SEPARACION_VERTICAL_MAXIMA
        return separacion

    def dibujar_grafo(self, marco_padre, mostrar_flujo=False, aristas_corte=None, conjunto_alcanzable=None, modo_color="ninguno"):
        grafo_dibujo = self.construir_grafo_networkx()

        if self.posiciones_layout is None:
            nivel_de_nodo = self.calcular_niveles_topologicos(grafo_dibujo)
            self.posiciones_layout = self.construir_posiciones_por_niveles(grafo_dibujo, nivel_de_nodo)

        self.calcular_radios_aristas(grafo_dibujo)

        aristas_ultimo_camino = []
        camino_por_arista = {}
        if modo_color == "ejecucion":
            if self.solucionador.terminado == False:
                aristas_ultimo_camino = self.solucionador.obtener_aristas_ultimo_camino()
        if modo_color == "camino":
            camino_por_arista = self.solucionador.obtener_camino_por_arista()

        elementos_leyenda = self.construir_elementos_leyenda(modo_color, aristas_corte, conjunto_alcanzable)

        figura = plt.Figure(figsize=(9.5, 6.4), dpi=100)
        if len(elementos_leyenda) > 0:
            ejes = figura.add_axes([0.0, 0.12, 1.0, 0.88])
        else:
            ejes = figura.add_axes([0.0, 0.0, 1.0, 1.0])

        colores_nodos = []
        for nombre in grafo_dibujo.nodes():
            if conjunto_alcanzable is not None and nombre in conjunto_alcanzable:
                colores_nodos.append(COLOR_NODO_ALCANZABLE)
            elif nombre == self.nodo_fuente_final:
                colores_nodos.append("#f4b183")
            elif nombre == self.nodo_sumidero_final:
                colores_nodos.append("#9dc3e6")
            else:
                colores_nodos.append("#d9d9d9")

        nx.draw_networkx_nodes(
            grafo_dibujo, self.posiciones_layout, ax=ejes,
            node_color=colores_nodos, node_size=700, edgecolors="black"
        )

        posiciones_etiquetas = self.construir_posiciones_etiquetas_nodos(grafo_dibujo)
        nx.draw_networkx_labels(grafo_dibujo, posiciones_etiquetas, ax=ejes, font_size=9)

        grupos_aristas = {}
        for arista in grafo_dibujo.edges():
            estilo = self.obtener_estilo_arista(arista, modo_color, aristas_corte, aristas_ultimo_camino, camino_por_arista)
            radio = self.radios_aristas[arista]
            if radio not in grupos_aristas:
                grupos_aristas[radio] = [[], [], []]
            grupos_aristas[radio][0].append(arista)
            grupos_aristas[radio][1].append(estilo[0])
            grupos_aristas[radio][2].append(estilo[1])

        for radio in grupos_aristas.keys():
            grupo = grupos_aristas[radio]
            self.dibujar_grupo_aristas(grafo_dibujo, ejes, grupo[0], grupo[1], grupo[2], radio)
        self.dibujar_etiquetas_aristas(ejes, mostrar_flujo)

        for parche in ejes.patches:
            parche.set_clip_on(False)

        self.ajustar_limites_ejes(ejes, grafo_dibujo)

        if len(elementos_leyenda) > 0:
            columnas_leyenda = 3
            if len(elementos_leyenda) > 6:
                columnas_leyenda = 4
            figura.legend(handles=elementos_leyenda, loc="lower center", ncol=columnas_leyenda, fontsize=8)

        ejes.set_axis_off()

        lienzo = FigureCanvasTkAgg(figura, master=marco_padre)
        lienzo.draw()
        widget_lienzo = lienzo.get_tk_widget()
        widget_lienzo.pack(fill="both", expand=True)
        return widget_lienzo

    def ajustar_limites_ejes(self, ejes, grafo_dibujo):
        coordenadas_x = []
        coordenadas_y = []

        for nombre in grafo_dibujo.nodes():
            coordenadas_x.append(self.posiciones_layout[nombre][0])
            coordenadas_y.append(self.posiciones_layout[nombre][1])

        for clave in self.grafo.capacidades.keys():
            punto_etiqueta = self.calcular_punto_etiqueta(clave)
            coordenadas_x.append(punto_etiqueta[0])
            coordenadas_y.append(punto_etiqueta[1])

        esquina_inferior = (min(coordenadas_x) - MARGEN_GRAFICO, min(coordenadas_y) - MARGEN_GRAFICO)
        esquina_superior = (max(coordenadas_x) + MARGEN_GRAFICO, max(coordenadas_y) + MARGEN_GRAFICO)

        ejes.margins(0)
        ejes.update_datalim([esquina_inferior, esquina_superior])
        ejes.autoscale_view()
        ejes.set_aspect("equal", adjustable="datalim")

    def construir_posiciones_etiquetas_nodos(self, grafo_dibujo):
        posiciones_etiquetas = {}
        for nombre in grafo_dibujo.nodes():
            posicion = self.posiciones_layout[nombre]
            if len(nombre) > 4:
                posiciones_etiquetas[nombre] = (posicion[0], posicion[1] - 0.45)
            else:
                posiciones_etiquetas[nombre] = posicion
        return posiciones_etiquetas

    def obtener_estilo_arista(self, arista, modo_color, aristas_corte, aristas_ultimo_camino, camino_por_arista):
        if modo_color == "ninguno":
            return COLOR_ARISTA_NORMAL, 1.2

        flujo = self.grafo.flujos[arista]

        if modo_color == "camino":
            if arista in camino_por_arista and flujo > 0:
                indice_color = (camino_por_arista[arista] - 1) % len(PALETA_CAMINOS)
                return PALETA_CAMINOS[indice_color], 2.6
            return COLOR_ARISTA_SIN_FLUJO, 1.2

        if aristas_corte is not None and arista in aristas_corte:
            return COLOR_ARISTA_CORTE, 3.2

        if self.grafo.esta_agotada(arista):
            return COLOR_ARISTA_AGOTADA, 2.8

        if arista in aristas_ultimo_camino:
            return COLOR_ARISTA_CAMINO_ACTUAL, 3.0

        if flujo > 0:
            return COLOR_ARISTA_PARCIAL, 2.0

        return COLOR_ARISTA_SIN_FLUJO, 1.2

    def construir_elementos_leyenda(self, modo_color, aristas_corte, conjunto_alcanzable):
        elementos = []

        if modo_color == "ninguno":
            return elementos

        if modo_color == "camino":
            numero_camino = 1
            for paso in self.solucionador.historial_caminos:
                indice_color = (numero_camino - 1) % len(PALETA_CAMINOS)
                texto_camino = "Camino " + str(numero_camino) + " (cantidad = " + str(paso["capacidad"]) + ")"
                elementos.append(Line2D([0], [0], color=PALETA_CAMINOS[indice_color], linewidth=2.6, label=texto_camino))
                numero_camino = numero_camino + 1
            elementos.append(Line2D([0], [0], color=COLOR_ARISTA_SIN_FLUJO, linewidth=1.5, label="Sin flujo"))
            return elementos

        if modo_color == "ejecucion":
            elementos.append(Line2D([0], [0], color=COLOR_ARISTA_CAMINO_ACTUAL, linewidth=3, label="Camino de aumento actual"))

        if aristas_corte is not None:
            elementos.append(Line2D([0], [0], color=COLOR_ARISTA_CORTE, linewidth=3, label="Agotada y parte del corte minimo"))

        elementos.append(Line2D([0], [0], color=COLOR_ARISTA_AGOTADA, linewidth=3, label="Agotada (flujo = capacidad)"))
        elementos.append(Line2D([0], [0], color=COLOR_ARISTA_PARCIAL, linewidth=2, label="Flujo parcial"))
        elementos.append(Line2D([0], [0], color=COLOR_ARISTA_SIN_FLUJO, linewidth=1.5, label="Sin flujo"))

        if conjunto_alcanzable is not None:
            elementos.append(Line2D(
                [0], [0], marker="o", linestyle="None", markerfacecolor=COLOR_NODO_ALCANZABLE,
                markeredgecolor="black", markersize=9, label="Nodo alcanzable desde la fuente"
            ))

        return elementos

    def es_arista_larga(self, arista):
        x_origen = self.posiciones_layout[arista[0]][0]
        x_destino = self.posiciones_layout[arista[1]][0]
        if abs(x_destino - x_origen) > DISTANCIA_ARISTA_LARGA:
            return True
        else:
            return False

    def obtener_radio_curva(self, arista):
        return self.radios_aristas[arista]

    def calcular_radios_aristas(self, grafo_dibujo):
        self.radios_aristas = {}
        for arista in grafo_dibujo.edges():
            if self.es_arista_larga(arista):
                self.radios_aristas[arista] = self.elegir_radio_arista_larga(arista, grafo_dibujo)
            else:
                self.radios_aristas[arista] = RADIO_CURVA_CORTA

    def elegir_radio_arista_larga(self, arista, grafo_dibujo):
        mejor_radio = CANDIDATOS_RADIO_LARGA[0]
        mejor_distancia = -1.0

        for radio in CANDIDATOS_RADIO_LARGA:
            distancia = self.calcular_distancia_minima_a_nodos(arista, radio, grafo_dibujo)
            if distancia >= DISTANCIA_LIBRE_NODOS:
                return radio
            if distancia > mejor_distancia:
                mejor_distancia = distancia
                mejor_radio = radio

        return mejor_radio

    def calcular_distancia_minima_a_nodos(self, arista, radio, grafo_dibujo):
        x_inicio = self.posiciones_layout[arista[0]][0]
        y_inicio = self.posiciones_layout[arista[0]][1]
        x_fin = self.posiciones_layout[arista[1]][0]
        y_fin = self.posiciones_layout[arista[1]][1]

        x_control = (x_inicio + x_fin) / 2.0 + radio * (y_fin - y_inicio)
        y_control = (y_inicio + y_fin) / 2.0 - radio * (x_fin - x_inicio)

        distancia_minima = 1000000.0
        for paso in range(1, 10):
            t = paso / 10.0
            x_curva = (1 - t) * (1 - t) * x_inicio + 2 * t * (1 - t) * x_control + t * t * x_fin
            y_curva = (1 - t) * (1 - t) * y_inicio + 2 * t * (1 - t) * y_control + t * t * y_fin

            for nombre in grafo_dibujo.nodes():
                if nombre != arista[0] and nombre != arista[1]:
                    diferencia_x = self.posiciones_layout[nombre][0] - x_curva
                    diferencia_y = self.posiciones_layout[nombre][1] - y_curva
                    distancia = math.sqrt(diferencia_x * diferencia_x + diferencia_y * diferencia_y)
                    if distancia < distancia_minima:
                        distancia_minima = distancia

        return distancia_minima

    def dibujar_grupo_aristas(self, grafo_dibujo, ejes, aristas, colores, anchos, radio_curva):
        if len(aristas) == 0:
            return
        nx.draw_networkx_edges(
            grafo_dibujo, self.posiciones_layout, ax=ejes, edgelist=aristas,
            edge_color=colores, width=anchos, arrowsize=14,
            connectionstyle="arc3,rad=" + str(radio_curva), node_size=700
        )

    def calcular_punto_etiqueta(self, clave):
        x_origen = self.posiciones_layout[clave[0]][0]
        y_origen = self.posiciones_layout[clave[0]][1]
        x_destino = self.posiciones_layout[clave[1]][0]
        y_destino = self.posiciones_layout[clave[1]][1]
        diferencia_x = x_destino - x_origen
        diferencia_y = y_destino - y_origen

        radio_curva = self.obtener_radio_curva(clave)
        x_etiqueta = (x_origen + x_destino) / 2.0 + 0.5 * radio_curva * diferencia_y
        y_etiqueta = (y_origen + y_destino) / 2.0 - 0.5 * radio_curva * diferencia_x
        return (x_etiqueta, y_etiqueta)

    def calcular_angulo_arista(self, clave):
        diferencia_x = self.posiciones_layout[clave[1]][0] - self.posiciones_layout[clave[0]][0]
        diferencia_y = self.posiciones_layout[clave[1]][1] - self.posiciones_layout[clave[0]][1]
        return math.degrees(math.atan2(diferencia_y, diferencia_x))

    def dibujar_etiquetas_aristas(self, ejes, mostrar_flujo):
        for clave in self.grafo.capacidades.keys():
            capacidad = self.grafo.capacidades[clave]
            if mostrar_flujo:
                texto_etiqueta = str(self.grafo.flujos[clave]) + " / " + str(capacidad)
            else:
                texto_etiqueta = str(capacidad)

            punto_etiqueta = self.calcular_punto_etiqueta(clave)
            angulo = self.calcular_angulo_arista(clave)

            ejes.text(
                punto_etiqueta[0], punto_etiqueta[1], texto_etiqueta, fontsize=8,
                ha="center", va="center", rotation=angulo, rotation_mode="anchor", zorder=5,
                clip_on=False, bbox=dict(boxstyle="round,pad=0.15", facecolor="white", edgecolor="white")
            )

    def mostrar_pantalla_seleccion(self):
        self.limpiar_contenedor()
        self.posiciones_layout = None
        self.nodos_seleccion = self.grafo.obtener_nodos_en_uso()

        self.crear_boton_atras(self.contenedor, self.regresar_desde_seleccion)

        titulo = tk.Label(self.contenedor, text="Seleccion de Vertice(s) Fuente y Sumidero", font=("Arial", 16, "bold"))
        titulo.pack(pady=10)

        marco_principal = tk.Frame(self.contenedor)
        marco_principal.pack(fill="both", expand=True, padx=10, pady=10)

        marco_grafo = tk.Frame(marco_principal)
        marco_grafo.pack(side="left", fill="both", expand=True)
        self.dibujar_grafo(marco_grafo)

        marco_lateral = tk.Frame(marco_principal)
        marco_lateral.pack(side="right", fill="y", padx=10)

        etiqueta_fuentes = tk.Label(marco_lateral, text="Vertice(s) fuente\n(puede seleccionar varios):", justify="left")
        etiqueta_fuentes.pack(anchor="w")

        self.lista_fuentes = tk.Listbox(marco_lateral, selectmode="multiple", height=6, exportselection=False)
        self.llenar_lista_nodos(self.lista_fuentes, self.fuentes_seleccionadas)
        self.lista_fuentes.pack(pady=5)

        etiqueta_sumideros = tk.Label(marco_lateral, text="Vertice(s) sumidero\n(puede seleccionar varios):", justify="left")
        etiqueta_sumideros.pack(anchor="w")

        self.lista_sumideros = tk.Listbox(marco_lateral, selectmode="multiple", height=6, exportselection=False)
        self.llenar_lista_nodos(self.lista_sumideros, self.sumideros_seleccionados)
        self.lista_sumideros.pack(pady=5)

        nota = tk.Label(
            marco_lateral,
            text="Si selecciona mas de una fuente o\nmas de un sumidero, el sistema\ncreara un nodo ficticio automaticamente.",
            justify="left", fg="#555555", font=("Arial", 9)
        )
        nota.pack(pady=5)

        marco_arista = tk.LabelFrame(marco_lateral, text="Agregar otra arista")
        marco_arista.pack(pady=5, fill="x")

        etiqueta_origen = tk.Label(marco_arista, text="Origen:")
        etiqueta_origen.grid(row=0, column=0, padx=5, pady=3, sticky="w")
        self.combo_origen_seleccion = ttk.Combobox(marco_arista, values=self.grafo.nombres_nodos, width=8, state="readonly")
        self.combo_origen_seleccion.grid(row=0, column=1, padx=5, pady=3)

        etiqueta_destino = tk.Label(marco_arista, text="Destino:")
        etiqueta_destino.grid(row=1, column=0, padx=5, pady=3, sticky="w")
        self.combo_destino_seleccion = ttk.Combobox(marco_arista, values=self.grafo.nombres_nodos, width=8, state="readonly")
        self.combo_destino_seleccion.grid(row=1, column=1, padx=5, pady=3)

        etiqueta_capacidad = tk.Label(marco_arista, text="Capacidad:")
        etiqueta_capacidad.grid(row=2, column=0, padx=5, pady=3, sticky="w")
        self.entrada_capacidad_seleccion = tk.Entry(marco_arista, width=10)
        self.entrada_capacidad_seleccion.grid(row=2, column=1, padx=5, pady=3)

        boton_agregar = tk.Button(marco_arista, text="Agregar arista", command=self.agregar_arista_desde_seleccion)
        boton_agregar.grid(row=3, column=0, columnspan=2, pady=5)

        boton_continuar = tk.Button(marco_lateral, text="Continuar", command=self.procesar_seleccion_fuente_sumidero, font=("Arial", 11, "bold"))
        boton_continuar.pack(pady=10)

    def llenar_lista_nodos(self, lista, nombres_seleccionados):
        indice = 0
        while indice < len(self.nodos_seleccion):
            nombre = self.nodos_seleccion[indice]
            lista.insert("end", nombre)
            if nombre in nombres_seleccionados:
                lista.selection_set(indice)
            indice = indice + 1

    def obtener_nombres_seleccionados(self, lista):
        nombres = []
        for indice in lista.curselection():
            nombres.append(self.nodos_seleccion[indice])
        return nombres

    def agregar_arista_desde_seleccion(self):
        origen = self.combo_origen_seleccion.get()
        destino = self.combo_destino_seleccion.get()
        texto_capacidad = self.entrada_capacidad_seleccion.get().strip()

        mensaje_error = self.validar_datos_arista(origen, destino, texto_capacidad)
        if mensaje_error != "":
            messagebox.showerror("Error", mensaje_error)
            return

        capacidad = int(texto_capacidad)
        self.grafo.agregar_arista(origen, destino, capacidad)

        if self.grafo.tiene_ciclo():
            self.grafo.eliminar_arista(origen, destino)
            messagebox.showerror(
                "Ciclo detectado",
                "Esa arista crearia un ciclo en el grafo.\n\n"
                "La red de flujo no debe contener ciclos, por lo que la arista no fue agregada."
            )
            return

        self.fuentes_seleccionadas = self.obtener_nombres_seleccionados(self.lista_fuentes)
        self.sumideros_seleccionados = self.obtener_nombres_seleccionados(self.lista_sumideros)
        self.mostrar_pantalla_seleccion()

    def regresar_desde_seleccion(self):
        modo = self.modo_construccion.get()
        if modo == "manual":
            self.mostrar_pantalla_manual()
        else:
            self.mostrar_pantalla_configuracion()

    def calcular_capacidad_saliente(self, nodo):
        total = 0
        for clave in self.grafo.capacidades.keys():
            origen = clave[0]
            if origen == nodo:
                total = total + self.grafo.capacidades[clave]
        return total

    def calcular_capacidad_entrante(self, nodo):
        total = 0
        for clave in self.grafo.capacidades.keys():
            destino = clave[1]
            if destino == nodo:
                total = total + self.grafo.capacidades[clave]
        return total

    def procesar_seleccion_fuente_sumidero(self):
        fuentes = self.obtener_nombres_seleccionados(self.lista_fuentes)
        sumideros = self.obtener_nombres_seleccionados(self.lista_sumideros)

        if len(fuentes) == 0 or len(sumideros) == 0:
            messagebox.showerror("Error", "Debe seleccionar al menos un vertice fuente y al menos un vertice sumidero.")
            return

        conjunto_fuentes = set(fuentes)
        conjunto_sumideros = set(sumideros)
        interseccion = conjunto_fuentes.intersection(conjunto_sumideros)
        if len(interseccion) > 0:
            messagebox.showerror("Error", "Un mismo vertice no puede ser fuente y sumidero al mismo tiempo.")
            return

        self.fuentes_seleccionadas = fuentes
        self.sumideros_seleccionados = sumideros

        self.respaldo_capacidades = dict(self.grafo.capacidades)
        self.respaldo_flujos = dict(self.grafo.flujos)
        self.respaldo_nombres_nodos = list(self.grafo.nombres_nodos)

        if len(fuentes) == 1:
            self.nodo_fuente_final = fuentes[0]
        else:
            nombre_ficticio = "Origen_Ficticio"
            self.grafo.agregar_nodo_ficticio(nombre_ficticio)
            for fuente in fuentes:
                capacidad_total = self.calcular_capacidad_saliente(fuente)
                if capacidad_total == 0:
                    capacidad_total = CAPACIDAD_MAXIMA
                self.grafo.agregar_arista(nombre_ficticio, fuente, capacidad_total)
            self.nodo_fuente_final = nombre_ficticio

        if len(sumideros) == 1:
            self.nodo_sumidero_final = sumideros[0]
        else:
            nombre_ficticio = "Destino_Ficticio"
            self.grafo.agregar_nodo_ficticio(nombre_ficticio)
            for sumidero in sumideros:
                capacidad_total = self.calcular_capacidad_entrante(sumidero)
                if capacidad_total == 0:
                    capacidad_total = CAPACIDAD_MAXIMA
                self.grafo.agregar_arista(sumidero, nombre_ficticio, capacidad_total)
            self.nodo_sumidero_final = nombre_ficticio

        self.posiciones_layout = None
        self.reporte_guardado = False
        self.ruta_reporte = ""
        self.solucionador = FordFulkerson(self.grafo, self.nodo_fuente_final, self.nodo_sumidero_final)
        self.mostrar_pantalla_ejecucion()

    def mostrar_pantalla_ejecucion(self):
        self.limpiar_contenedor()

        if hasattr(self, "boton_resultado_final"):
            delattr(self, "boton_resultado_final")

        self.crear_boton_atras(self.contenedor, self.regresar_desde_ejecucion)

        titulo_texto = "Ejecucion del Algoritmo  |  Fuente: " + self.nodo_fuente_final + "   Sumidero: " + self.nodo_sumidero_final
        titulo = tk.Label(self.contenedor, text=titulo_texto, font=("Arial", 14, "bold"))
        titulo.pack(pady=10)

        marco_principal = tk.Frame(self.contenedor)
        marco_principal.pack(fill="both", expand=True, padx=10, pady=5)
        self.marco_principal_ejecucion = marco_principal

        self.marco_grafo_ejecucion = tk.Frame(marco_principal)
        self.marco_grafo_ejecucion.pack(side="left", fill="both", expand=True)
        self.dibujar_grafo(self.marco_grafo_ejecucion, mostrar_flujo=True, modo_color="ejecucion")

        marco_lateral = tk.Frame(marco_principal)
        marco_lateral.pack(side="right", fill="y", padx=10)

        self.etiqueta_flujo_total = tk.Label(marco_lateral, text="Flujo total acumulado: " + str(self.solucionador.flujo_total), font=("Arial", 12, "bold"))
        self.etiqueta_flujo_total.pack(pady=10)

        etiqueta_registro = tk.Label(marco_lateral, text="Registro de ejecucion:")
        etiqueta_registro.pack(anchor="w")

        self.area_registro = scrolledtext.ScrolledText(marco_lateral, width=48, height=24)
        self.area_registro.pack(pady=5)

        for paso_anterior in self.solucionador.historial_caminos:
            self.area_registro.insert("end", self.formatear_linea_paso(paso_anterior))
        if self.solucionador.terminado:
            self.area_registro.insert("end", "No se encontraron mas caminos de aumento.\nEl algoritmo ha finalizado.\n\n")
            if self.ruta_reporte != "":
                self.area_registro.insert("end", "Reporte guardado en:\n" + self.ruta_reporte + "\n\n")
        self.area_registro.see("end")

        marco_botones = tk.Frame(marco_lateral)
        marco_botones.pack(pady=10)

        boton_siguiente = tk.Button(marco_botones, text="Siguiente Paso", command=self.ejecutar_siguiente_paso)
        boton_siguiente.pack(side="left", padx=5)

        boton_completo = tk.Button(marco_botones, text="Ejecutar Todo", command=self.ejecutar_todo)
        boton_completo.pack(side="left", padx=5)

        if self.solucionador.terminado:
            self.mostrar_boton_resultado_final()

    def regresar_desde_ejecucion(self):
        if self.respaldo_capacidades is not None:
            self.grafo.capacidades = dict(self.respaldo_capacidades)
            self.grafo.flujos = dict(self.respaldo_flujos)
            self.grafo.nombres_nodos = list(self.respaldo_nombres_nodos)

        self.nodo_fuente_final = None
        self.nodo_sumidero_final = None
        self.solucionador = None
        self.posiciones_layout = None
        self.mostrar_pantalla_seleccion()

    def formatear_linea_paso(self, resultado_paso):
        camino_texto = " -> ".join(resultado_paso["camino"])
        linea = "Camino de aumento encontrado:\n   " + camino_texto + "\n"
        linea = linea + "Capacidad residual minima (cuello de botella): " + str(resultado_paso["capacidad"]) + "\n"
        linea = linea + "Flujo acumulado hasta el momento: " + str(resultado_paso["flujo_acumulado"]) + "\n"
        linea = linea + "Aristas agotadas en este paso: " + self.formatear_lista_aristas(resultado_paso["agotadas"]) + "\n\n"
        return linea

    def formatear_lista_aristas(self, aristas):
        if len(aristas) == 0:
            return "ninguna"
        textos = []
        for arista in aristas:
            textos.append(arista[0] + " -> " + arista[1])
        return ", ".join(textos)

    def ejecutar_siguiente_paso(self):
        if self.solucionador.terminado:
            messagebox.showinfo("Informacion", "El algoritmo ya finalizo. Presione 'Ver Resultado Final'.")
            return

        resultado_paso = self.solucionador.ejecutar_un_paso()

        if resultado_paso is None:
            self.finalizar_ejecucion()
            return

        linea_registro = self.formatear_linea_paso(resultado_paso)
        self.area_registro.insert("end", linea_registro)
        self.area_registro.see("end")

        self.etiqueta_flujo_total.config(text="Flujo total acumulado: " + str(self.solucionador.flujo_total))
        self.redibujar_grafo_ejecucion()

    def redibujar_grafo_ejecucion(self):
        lista_hijos = self.marco_grafo_ejecucion.winfo_children()
        for hijo in lista_hijos:
            hijo.destroy()
        self.dibujar_grafo(self.marco_grafo_ejecucion, mostrar_flujo=True, modo_color="ejecucion")

    def ejecutar_todo(self):
        if self.solucionador.terminado:
            messagebox.showinfo("Informacion", "El algoritmo ya finalizo. Presione 'Ver Resultado Final'.")
            return

        while self.solucionador.terminado == False:
            resultado_paso = self.solucionador.ejecutar_un_paso()
            if resultado_paso is not None:
                linea_registro = self.formatear_linea_paso(resultado_paso)
                self.area_registro.insert("end", linea_registro)

        self.finalizar_ejecucion()

    def finalizar_ejecucion(self):
        self.area_registro.insert("end", "No se encontraron mas caminos de aumento.\nEl algoritmo ha finalizado.\n\n")

        self.etiqueta_flujo_total.config(text="Flujo total acumulado: " + str(self.solucionador.flujo_total))
        self.redibujar_grafo_ejecucion()

        self.guardar_reporte_txt()
        if self.ruta_reporte != "":
            self.area_registro.insert("end", "Reporte guardado en:\n" + self.ruta_reporte + "\n\n")
        self.area_registro.see("end")

        self.mostrar_boton_resultado_final()

    def mostrar_boton_resultado_final(self):
        if hasattr(self, "boton_resultado_final"):
            return

        self.boton_resultado_final = tk.Button(
            self.contenedor, text="Ver Resultado Final",
            command=self.mostrar_pantalla_resultado,
            font=("Arial", 11, "bold"), bg="#70ad47", fg="white"
        )
        self.boton_resultado_final.pack(side="bottom", pady=10, before=self.marco_principal_ejecucion)

    def mostrar_pantalla_resultado(self):
        self.limpiar_contenedor()
        self.modo_vista_resultado = "estado"

        self.crear_boton_atras(self.contenedor, self.mostrar_pantalla_ejecucion)

        titulo = tk.Label(self.contenedor, text="Resultado Final: Flujo Maximo y Corte Minimo", font=("Arial", 16, "bold"))
        titulo.pack(pady=10)

        marco_principal = tk.Frame(self.contenedor)
        marco_principal.pack(fill="both", expand=True, padx=10, pady=10)

        self.marco_grafo_resultado = tk.Frame(marco_principal)
        self.marco_grafo_resultado.pack(side="left", fill="both", expand=True)
        self.redibujar_grafo_resultado()

        marco_lateral = tk.Frame(marco_principal)
        marco_lateral.pack(side="right", fill="y", padx=10)

        self.boton_vista_resultado = tk.Button(marco_lateral, text="Ver por camino de aumento", command=self.cambiar_vista_resultado)
        self.boton_vista_resultado.pack(pady=5)

        area_resumen = scrolledtext.ScrolledText(marco_lateral, width=52, height=30)
        area_resumen.pack(pady=5)

        texto_resumen = self.construir_texto_resumen()
        if self.ruta_reporte != "":
            texto_resumen = texto_resumen + "\nREPORTE GUARDADO EN:\n" + self.ruta_reporte + "\n"

        area_resumen.insert("end", texto_resumen)
        area_resumen.config(state="disabled")

    def redibujar_grafo_resultado(self):
        lista_hijos = self.marco_grafo_resultado.winfo_children()
        for hijo in lista_hijos:
            hijo.destroy()

        resultado_corte = self.solucionador.calcular_corte_minimo()
        aristas_corte = resultado_corte[0]
        conjunto_alcanzable = resultado_corte[1]

        self.dibujar_grafo(
            self.marco_grafo_resultado, mostrar_flujo=True, aristas_corte=aristas_corte,
            conjunto_alcanzable=conjunto_alcanzable, modo_color=self.modo_vista_resultado
        )

    def cambiar_vista_resultado(self):
        if self.modo_vista_resultado == "estado":
            self.modo_vista_resultado = "camino"
            self.boton_vista_resultado.config(text="Ver por estado de las aristas")
        else:
            self.modo_vista_resultado = "estado"
            self.boton_vista_resultado.config(text="Ver por camino de aumento")
        self.redibujar_grafo_resultado()

    def construir_texto_resumen(self):
        resultado_corte = self.solucionador.calcular_corte_minimo()
        aristas_corte = resultado_corte[0]

        texto_resumen = "VALOR DEL FLUJO MAXIMO: " + str(self.solucionador.flujo_total) + "\n\n"

        texto_resumen = texto_resumen + "CAMINOS DE AUMENTO UTILIZADOS:\n"
        contador = 1
        for paso in self.solucionador.historial_caminos:
            camino_texto = " -> ".join(paso["camino"])
            texto_resumen = texto_resumen + str(contador) + ". " + camino_texto + "   (cantidad = " + str(paso["capacidad"]) + ")\n"
            contador = contador + 1

        texto_resumen = texto_resumen + "\nFLUJO FINAL EN CADA ARISTA:\n"
        for clave in self.grafo.capacidades.keys():
            origen = clave[0]
            destino = clave[1]
            capacidad = self.grafo.capacidades[clave]
            flujo = self.grafo.flujos[clave]
            texto_resumen = texto_resumen + origen + " -> " + destino + " :  " + str(flujo) + " / " + str(capacidad)
            if self.grafo.esta_agotada(clave):
                texto_resumen = texto_resumen + "   [AGOTADA]"
            texto_resumen = texto_resumen + "\n"

        texto_resumen = texto_resumen + "\nARISTAS AGOTADAS (flujo = capacidad):\n"
        aristas_agotadas = self.grafo.obtener_aristas_agotadas()
        if len(aristas_agotadas) == 0:
            texto_resumen = texto_resumen + "Ninguna\n"
        for clave in aristas_agotadas:
            capacidad = self.grafo.capacidades[clave]
            texto_resumen = texto_resumen + clave[0] + " -> " + clave[1] + "   (capacidad = " + str(capacidad) + ")\n"

        texto_resumen = texto_resumen + "\nCORTE MINIMO (aristas que lo componen):\n"
        suma_capacidades_corte = 0
        for clave in aristas_corte:
            origen = clave[0]
            destino = clave[1]
            capacidad = self.grafo.capacidades[clave]
            suma_capacidades_corte = suma_capacidades_corte + capacidad
            texto_resumen = texto_resumen + origen + " -> " + destino + "   (capacidad = " + str(capacidad) + ")\n"

        texto_resumen = texto_resumen + "\nSuma de capacidades del corte minimo: " + str(suma_capacidades_corte) + "\n"
        if suma_capacidades_corte == self.solucionador.flujo_total:
            texto_resumen = texto_resumen + "Esta suma coincide con el flujo maximo, lo cual verifica\n"
            texto_resumen = texto_resumen + "el teorema de flujo maximo - corte minimo.\n"
        else:
            texto_resumen = texto_resumen + "ATENCION: la suma no coincide con el flujo maximo.\n"

        return texto_resumen

    def formatear_aristas_con_flujo(self, aristas):
        if len(aristas) == 0:
            return "  Ninguna\n"
        texto_aristas = ""
        for clave in aristas:
            capacidad = self.grafo.capacidades[clave]
            flujo = self.grafo.flujos[clave]
            texto_aristas = texto_aristas + "  " + clave[0] + " -> " + clave[1] + " :  " + str(flujo) + " / " + str(capacidad) + "\n"
        return texto_aristas

    def construir_texto_reporte(self):
        separador = "================================================================\n"
        resultado_corte = self.solucionador.calcular_corte_minimo()
        conjunto_alcanzable = resultado_corte[1]

        if self.modo_construccion.get() == "manual":
            texto_modo = "Manual"
        else:
            texto_modo = "Aleatorio"

        texto = separador
        texto = texto + "REPORTE DEL PROBLEMA DEL FLUJO MAXIMO (FORD-FULKERSON)\n"
        texto = texto + separador
        texto = texto + "Fecha y hora: " + datetime.now().strftime("%d/%m/%Y %H:%M:%S") + "\n"
        texto = texto + NOMBRE_UNIVERSIDAD_LINEA_1 + " - " + NOMBRE_UNIVERSIDAD_LINEA_2 + "\n"
        texto = texto + "Integrantes:\n"
        for nombre_integrante in NOMBRES_INTEGRANTES:
            texto = texto + "  - " + nombre_integrante + "\n"

        texto = texto + "\n" + separador + "1. DATOS DEL PROBLEMA\n" + separador
        texto = texto + "Modo de construccion del grafo: " + texto_modo + "\n"
        texto = texto + "Cantidad de nodos configurada: " + str(self.cantidad_nodos) + "\n"
        texto = texto + "Cantidad de aristas del grafo: " + str(len(self.respaldo_capacidades)) + "\n\n"
        texto = texto + "Aristas del grafo (origen -> destino, capacidad):\n"
        for clave in self.respaldo_capacidades.keys():
            capacidad = self.respaldo_capacidades[clave]
            texto = texto + "  " + clave[0] + " -> " + clave[1] + "   (capacidad = " + str(capacidad) + ")\n"

        texto = texto + "\nVertice(s) fuente seleccionado(s): " + ", ".join(self.fuentes_seleccionadas) + "\n"
        texto = texto + "Vertice(s) sumidero seleccionado(s): " + ", ".join(self.sumideros_seleccionados) + "\n"
        texto = texto + "Fuente usada por el algoritmo: " + self.nodo_fuente_final + "\n"
        texto = texto + "Sumidero usado por el algoritmo: " + self.nodo_sumidero_final + "\n"

        aristas_ficticias = []
        for clave in self.grafo.capacidades.keys():
            if clave not in self.respaldo_capacidades:
                aristas_ficticias.append(clave)
        if len(aristas_ficticias) > 0:
            texto = texto + "\nAristas agregadas por los nodos ficticios:\n"
            for clave in aristas_ficticias:
                capacidad = self.grafo.capacidades[clave]
                texto = texto + "  " + clave[0] + " -> " + clave[1] + "   (capacidad = " + str(capacidad) + ")\n"

        texto = texto + "\n" + separador + "2. EJECUCION PASO A PASO\n" + separador
        numero_paso = 1
        for paso in self.solucionador.historial_caminos:
            texto = texto + "Paso " + str(numero_paso) + "\n"
            texto = texto + "  Camino de aumento: " + " -> ".join(paso["camino"]) + "\n"
            texto = texto + "  Cuello de botella (capacidad residual minima): " + str(paso["capacidad"]) + "\n"
            texto = texto + "  Flujo acumulado: " + str(paso["flujo_acumulado"]) + "\n"
            texto = texto + "  Aristas agotadas en este paso: " + self.formatear_lista_aristas(paso["agotadas"]) + "\n\n"
            numero_paso = numero_paso + 1
        texto = texto + "No se encontraron mas caminos de aumento. El algoritmo finalizo.\n"

        texto = texto + "\n" + separador + "3. RESULTADO FINAL\n" + separador
        texto = texto + self.construir_texto_resumen()

        aristas_parciales = []
        aristas_sin_flujo = []
        for clave in self.grafo.capacidades.keys():
            if self.grafo.esta_agotada(clave) == False:
                if self.grafo.flujos[clave] > 0:
                    aristas_parciales.append(clave)
                else:
                    aristas_sin_flujo.append(clave)

        texto = texto + "\n" + separador + "4. ESTADO DE LAS DEMAS ARISTAS\n" + separador
        texto = texto + "Aristas con flujo parcial (0 < flujo < capacidad):\n"
        texto = texto + self.formatear_aristas_con_flujo(aristas_parciales)
        texto = texto + "\nAristas sin flujo (no se uso ninguna):\n"
        texto = texto + self.formatear_aristas_con_flujo(aristas_sin_flujo)

        nodos_lado_fuente = []
        nodos_lado_sumidero = []
        for nombre in self.grafo.obtener_nodos_en_uso():
            if nombre in conjunto_alcanzable:
                nodos_lado_fuente.append(nombre)
            else:
                nodos_lado_sumidero.append(nombre)

        texto = texto + "\n" + separador + "5. CONJUNTOS DEL CORTE MINIMO\n" + separador
        texto = texto + "Conjunto S (alcanzables desde la fuente en el grafo residual):\n  " + ", ".join(nodos_lado_fuente) + "\n"
        texto = texto + "Conjunto T (resto de los nodos):\n  " + ", ".join(nodos_lado_sumidero) + "\n"

        texto = texto + "\n" + separador + "6. LEYENDA DE COLORES DEL GRAFO\n" + separador
        texto = texto + "  Gris     : arista sin flujo\n"
        texto = texto + "  Azul     : arista con flujo parcial\n"
        texto = texto + "  Naranja  : arista agotada (flujo = capacidad)\n"
        texto = texto + "  Morado   : camino de aumento actual (solo durante la ejecucion)\n"
        texto = texto + "  Rojo     : arista agotada que forma parte del corte minimo\n"
        texto = texto + "  Nodo verde: nodo alcanzable desde la fuente\n"
        texto = texto + "  Vista por camino: cada camino de aumento usa un color distinto;\n"
        texto = texto + "  si varios caminos pasaron por una arista, se pinta con el ultimo.\n"

        return texto

    def guardar_reporte_txt(self):
        if self.reporte_guardado:
            return

        marca_de_tiempo = datetime.now().strftime("%Y%m%d_%H%M%S")
        nombre_archivo = NOMBRE_BASE_REPORTE + "_" + marca_de_tiempo + ".txt"
        carpeta = os.path.dirname(os.path.abspath(__file__))
        ruta_archivo = os.path.join(carpeta, nombre_archivo)

        try:
            with open(ruta_archivo, "w", encoding="utf-8") as archivo:
                archivo.write(self.construir_texto_reporte())
        except OSError:
            messagebox.showerror("Error", "No se pudo guardar el reporte en:\n" + ruta_archivo)
            return

        self.reporte_guardado = True
        self.ruta_reporte = ruta_archivo

if __name__ == "__main__":
    aplicacion = AplicacionFlujoMaximo()
    aplicacion.mainloop()
