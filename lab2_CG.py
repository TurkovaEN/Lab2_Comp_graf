import math                                   # математика: корни, округления, синусы
import sys                                    # аргументы командной строки
import time                                   # время: замер длительности обработки
import random                                 # генерация случайных многоугольников
import tkinter as tk                          # графическая библиотека для отрисовки
import tkinter.font as tkfont                 # измерение текста для переносов строк


# параметры растра
SCREEN = 32                                   # размер растра: 32 x 32 пиксела
XMIN = -1e9                                   # начальное значение строки z-буфера (дальний план)


# параметры окна
WIN_W = 1296                                  # стартовая ширина окна
WIN_H = 880                                   # стартовая высота окна
CANVAS_W = 1280                               # ширина холста
CANVAS_H = 740                                # высота холста
AUTO_MS = 240                                 # период автоматической строки, миллисекунды


# параметры камеры
CAM_YAW = -38.0                               # начальный поворот камеры (градусы)
CAM_PITCH = 22.0                              # начальный наклон камеры (градусы)
CAM_ZOOM = 1.0                                # начальный масштаб камеры
CAM_YAW_STEP = 0.45                           # градусов поворота на пиксель мыши
CAM_PITCH_STEP = 0.35                         # градусов наклона на пиксель мыши
CAM_PITCH_LIMIT = 75.0                        # предельный наклон камеры


# цвета холста и панелей
CANVAS_BG = "#0e0e14"                         # фон холста — почти чёрный
TITLE_COLOR = "#e8e8f0"                       # цвет заголовков блоков
TEXT_COLOR = "#d0d0d8"                        # обычный текст
MUTED_COLOR = "#8a8aa8"                       # приглушённый служебный текст
EDGE_DIM = "#3c3c4c"                          # неактивные рёбра сцены (тусклые)
EDGE_ACTIVE = "#ffa726"                       # рёбра из списка активных (оранжевые)
EDGE_VISIBLE = "#fff2a8"                      # видимые пикселы рёбер (светло-жёлтые)
SCANLINE_COLOR = "#ffe082"                    # линия текущей сканирующей строки
INTERVAL_COLOR = "#69f0ae"                    # подсветка обрабатываемого интервала
SPLIT_COLOR = "#ff5252"                       # отметка точки разбиения интервала
CROSS_COLOR = "#ff5252"                       # точки пересечения строки с рёбрами


# цвета и размер триады осей
AXIS_COLOR_X = "#ff6b6b"                      # ось X — красная
AXIS_COLOR_Y = "#7bed7b"                      # ось Y — зелёная
AXIS_COLOR_Z = "#6bb6ff"                      # ось Z — синяя
AXIS_LEN = 25.0                               # длина стрелки оси на холсте
AXIS_BOX = 40                                 # половина стороны подложки триады


# цвета многоугольников (по индексу атрибута 1..6)
POLY_COLORS = ["#e57373",                      # 1 — красноватый
               "#81c784",                      # 2 — зеленоватый
               "#64b5f6",                      # 3 — синеватый
               "#ffd54f",                      # 4 — жёлтый
               "#ba68c8",                      # 5 — сиреневый
               "#4db6ac"]                      # 6 — бирюзовый


# геометрия блоков на холсте
SCENE_X = 20                                  # левый край области сцены
SCENE_Y = 56                                  # верхний край области сцены
SCENE_CELL = 16                               # размер пиксела растра на холсте
ZBUF_X = 560                                  # левый край панели z-буфера
ZBUF_Y = 56                                   # верхний край панели z-буфера
ZBUF_CELL = 9                                 # размер ячейки z-буфера на холсте
AEL_X = 560                                   # левый край таблицы активных рёбер
AEL_Y = 448                                   # верхний край таблицы активных рёбер
LOG_X = 880                                   # левый край панели хода выполнения
LOG_Y = 56                                    # верхний край панели хода выполнения
VERT_X = 880                                  # левый край списка координат вершин
VERT_Y = 464                                  # верхний край списка координат вершин
LOG_LINES = 19                                # сколько строк журнала помещается в панель


# идентификатор сцены из сгенерированных многоугольников по умолчанию
DEFAULT_SEED = 9                              # начальное зерно генератора случайных чисел


# уравнение плоскости по трём точкам: n = (p2 - p1) x (p3 - p1)
def plane_from_points(p1, p2, p3):
    ux = p2[0] - p1[0]                        # компонента вектора p2 - p1 по X
    uy = p2[1] - p1[1]                        # компонента вектора p2 - p1 по Y
    uz = p2[2] - p1[2]                        # компонента вектора p2 - p1 по Z
    vx = p3[0] - p1[0]                        # компонента вектора p3 - p1 по X
    vy = p3[1] - p1[1]                        # компонента вектора p3 - p1 по Y
    vz = p3[2] - p1[2]                        # компонента вектора p3 - p1 по Z
    a = uy * vz - uz * vy                     # X-компонента векторного произведения
    b = uz * vx - ux * vz                     # Y-компонента векторного произведения
    c = ux * vy - uy * vx                     # Z-компонента векторного произведения
    d = -(a * p1[0] + b * p1[1] + c * p1[2])  # свободный член из условия n * p1 + d = 0
    return (a, b, c, d)                       # коэффициенты плоскости a*x + b*y + c*z + d = 0


# глубина точки сканирующей строки: z = -(a*x + b*y + d) / c
def plane_z(plane, x, y):
    a, b, c, d = plane                       # распаковываем коэффициенты плоскости
    return -(a * x + b * y + d) / c           # выражаем z из уравнения плоскости


# многоугольник: номер (1..6), цвет и список вершин
def make_polygon(pid, verts):
    return {"id": pid,                        # номер многоугольника = атрибут цвета
            "color": POLY_COLORS[(pid - 1) % len(POLY_COLORS)],   # цвет по номеру
            "verts": verts,                   # вершины (x, y, z)
            "plane": plane_from_points(verts[0], verts[1], verts[2])}   # несущая плоскость


# тестовая сцена: треугольник протыкает прямоугольник
def scene_triangle_vs_rect():
    rect = [(10.0, 5.0, 10.0),                # левый нижний угол прямоугольника
            (10.0, 25.0, 10.0),               # левый верхний угол
            (25.0, 25.0, 10.0),               # правый верхний угол
            (25.0, 5.0, 10.0)]                # правый нижний угол
    tri = [(15.0, 15.0, 15.0),                # вершина треугольника перед плоскостью
            (25.0, 25.0, 5.0),                # вершина за плоскостью (правая верхняя)
            (30.0, 10.0, 5.0)]                # вершина за плоскостью (правая нижняя)
    polys = [make_polygon(1, rect),           # многоугольник 1 — прямоугольник
             make_polygon(2, tri)]            # многоугольник 2 — треугольник
    return {"name": "Тест 1: треугольник протыкает прямоугольник", "polys": polys}


# тестовая сцена: два треугольника протыкают друг друга
def scene_two_triangles():
    a = [(7.0, 5.0, 12.0),                    # первый треугольник — плоскость z = 12
         (25.0, 5.0, 12.0),                   # правый нижний угол
         (16.0, 27.0, 12.0)]                  # верхняя вершина
    b = [(7.0, 26.0, 9.0),                    # второй треугольник — наклонная плоскость
         (26.0, 23.0, 18.05),                 # правая вершина ближе к наблюдателю
         (16.0, 4.0, 10.2)]                   # нижняя вершина за плоскостью
    polys = [make_polygon(1, a),              # многоугольник 1 — первый треугольник
             make_polygon(2, b)]              # многоугольник 2 — второй треугольник
    return {"name": "Тест 2: два треугольника протыкают друг друга", "polys": polys}


# сгенерированная сцена: 5–6 многоугольников по 3–6 рёбер вокруг общего центра
def scene_generated(seed):
    rnd = random.Random(seed)                 # генератор со своим зерном
    count = rnd.randint(5, 6)                 # число многоугольников: 5 или 6
    sizes = [3, 4, 5, 6, 4, 5]                # набор возможных чисел рёбер
    rnd.shuffle(sizes)                        # перемешиваем набор для разнообразия
    cx0, cy0, cz0 = 16.0, 16.0, 10.0          # общий центр композиции сцены
    polys = []                                # список многоугольников сцены
    for i in range(count):                    # создаём каждый многоугольник
        nv = sizes[i]                         # число вершин: от 3 до 6
        rad = rnd.uniform(6.5, 9.5)           # радиус локального контура
        angs = sorted(rnd.uniform(0.0, 2.0 * math.pi) for _ in range(nv))   # углы вершин
        ax = math.radians(rnd.uniform(-55.0, 55.0))      # наклон контура вокруг X
        ay = math.radians(rnd.uniform(-70.0, 70.0))      # поворот контура вокруг Y
        az = math.radians(rnd.uniform(-180.0, 180.0))    # поворот контура вокруг Z
        verts = []                            # вершины многоугольника
        for ang in angs:                      # обходим локальный контур
            rr = rad * rnd.uniform(0.75, 1.0)        # радиус текущей вершины
            x = rr * math.cos(ang)            # локальная координата X
            y = rr * math.sin(ang)            # локальная координата Y
            z = 0.0                           # локальный контур лежит в плоскости XY
            x1 = x * math.cos(az) - y * math.sin(az)     # поворот вокруг оси Z
            y1 = x * math.sin(az) + y * math.cos(az)     # поворот вокруг оси Z
            y2 = y1 * math.cos(ax) - z * math.sin(ax)    # поворот вокруг оси X
            z2 = y1 * math.sin(ax) + z * math.cos(ax)    # поворот вокруг оси X
            x3 = x1 * math.cos(ay) + z2 * math.sin(ay)   # поворот вокруг оси Y
            z3 = -x1 * math.sin(ay) + z2 * math.cos(ay)  # поворот вокруг оси Y
            verts.append((round(cx0 + x3, 1),           # координата X вершины
                          round(cy0 + y2, 1),           # координата Y вершины
                          round(cz0 + z3, 1)))          # координата Z вершины
        polys.append(make_polygon(i + 1, verts))        # фиксируем многоугольник
    return {"name": "Сгенерированные многоугольники (зерно %d)" % seed, "polys": polys}


# удвоенная площадь многоугольника (формула шнуровки в проекции XY)
def area2(verts):
    s = 0.0                                   # накопитель суммы
    n = len(verts)                            # число вершин
    for i in range(n):                        # проходим по парам соседних вершин
        x1, y1 = verts[i][0], verts[i][1]     # координаты текущей вершины
        x2, y2 = verts[(i + 1) % n][0], verts[(i + 1) % n][1]   # координаты следующей
        s += x1 * y2 - x2 * y1                # слагаемое шнуровки
    return abs(s)                             # площадь с точностью до знака


# точка внутри многоугольника (трассировка луча в проекции XY)
def point_in_polygon(px, py, verts):
    inside = False                            # флаг «точка внутри»
    n = len(verts)                            # число вершин
    j = n - 1                                 # предыдущая вершина для ребра j–i
    for i in range(n):                        # перебираем рёбра многоугольника
        xi, yi = verts[i][0], verts[i][1]     # координаты текущей вершины
        xj, yj = verts[j][0], verts[j][1]     # координаты предыдущей вершины
        if (yi > py) != (yj > py):            # ребро пересекает горизонталь точки
            xcross = xi + (py - yi) * (xj - xi) / (yj - yi)     # X пересечения ребра
            if px < xcross:                   # точка левее пересечения
                inside = not inside           # смена чётности — внутри/снаружи
        j = i                                 # сдвигаем предыдущую вершину
    return inside                             # результат проверки


# сборка рёбер сцены для списка активных рёбер
def build_edges(scene):
    edges = []                                # итоговый список рёбер
    for poly in scene["polys"]:               # перебираем многоугольники сцены
        verts = poly["verts"]                 # вершины многоугольника
        n = len(verts)                        # число вершин
        for i in range(n):                    # перебираем стороны многоугольника
            p1 = verts[i]                     # начало стороны
            p2 = verts[(i + 1) % n]           # конец стороны
            label = "V%d-V%d" % (i, (i + 1) % n)     # подпись ребра по номерам вершин
            x1, y1 = p1[0], p1[1]             # проекция начала ребра
            x2, y2 = p2[0], p2[1]             # проекция конца ребра
            if abs(y1 - y2) < 1e-9:           # горизонтальные рёбра не пересекают строки
                edges.append({"pid": poly["id"], "label": label, "horizontal": True,
                              "y": y1, "lo": min(x1, x2), "hi": max(x1, x2),
                              "row_h": horizontal_row(poly, i, (i + 1) % n)})   # кладём ребро
                continue                      # к следующей стороне
            if y1 > y2:                       # верхний конец — с большей Y
                top, bot = p1, p2             # верхняя и нижняя точки ребра
            else:
                top, bot = p2, p1             # меняем порядок точек
            step = -(bot[0] - top[0]) / (bot[1] - top[1])   # шаг X при спуске на строку
            first_row = int(math.ceil(top[1] - 0.5)) - 1    # верхняя строка ребра
            last_row = int(math.ceil(bot[1] - 0.5))         # нижняя строка ребра
            edges.append({"pid": poly["id"], "label": label, "horizontal": False,
                          "top": top, "bot": bot, "step": step,
                          "first_row": first_row, "last_row": last_row})   # кладём ребро
    return edges                              # готовый список рёбер


# абсцисса ребра на строке с центром yc
def edge_x_at(e, yc):
    top, bot = e["top"], e["bot"]             # концы ребра: верхний и нижний
    return top[0] + (yc - top[1]) * (bot[0] - top[0]) / (bot[1] - top[1])   # линейная интерполяция


# строка растра для горизонтального ребра: ближайшая внутренняя строка многоугольника
def horizontal_row(poly, i, j):
    verts = poly["verts"]                     # вершины многоугольника
    n = len(verts)                            # число вершин
    y = verts[i][1]                           # высота ребра
    ys = [verts[k][1] for k in range(n) if k != i and k != j]    # высоты других вершин
    avg = sum(ys) / len(ys) if ys else y      # средняя высота остальных вершин
    if avg < y:                               # многоугольник лежит ниже ребра
        row = int(math.ceil(y - 0.5)) - 1     # ближайшая строка внутри многоугольника
    else:                                     # многоугольник лежит выше ребра
        row = int(math.ceil(y + 0.5)) - 1     # тоже ближайшая внутренняя строка
    return min(max(row, 0), SCREEN - 1)       # ограничиваем строку рамками растра


# список пикселов строки, центры которых лежат в полосе [a, b)
def pixel_span(a, b):
    return [x for x in range(SCREEN)         # перебираем все пикселы строки
            if x + 0.5 >= a - 1e-9 and x + 0.5 < b - 1e-9]   # центр внутри полосы


# поворот точки вокруг центра сцены: сначала наклон вокруг X, затем поворот вокруг Y
def rotate_point(x, y, z, yaw, pitch):
    cp = math.cos(pitch)                      # косинус наклона камеры
    sp = math.sin(pitch)                      # синус наклона камеры
    cy = math.cos(yaw)                        # косинус поворота камеры
    sy = math.sin(yaw)                        # синус поворота камеры
    y1 = y * cp - z * sp                      # наклон вокруг оси X
    z1 = y * sp + z * cp                      # наклон вокруг оси X
    x2 = x * cy + z1 * sy                     # поворот вокруг оси Y
    z2 = -x * sy + z1 * cy                    # поворот вокруг оси Y
    return x2, y1, z2                         # координаты после поворота


# вид камерой: поворот сцены, вписывание в растр и ортогональная проекция
def camera_scene(scene, yaw_deg, pitch_deg, zoom):
    yaw = math.radians(yaw_deg)               # поворот камеры в радианах
    pitch = math.radians(pitch_deg)           # наклон камеры в радианах
    verts = [v for p in scene["polys"] for v in p["verts"]]      # все вершины сцены
    xs = [v[0] for v in verts]                # координаты X всех вершин
    ys = [v[1] for v in verts]                # координаты Y всех вершин
    zs = [v[2] for v in verts]                # координаты Z всех вершин
    cx = (min(xs) + max(xs)) / 2.0            # центр сцены по X
    cy = (min(ys) + max(ys)) / 2.0            # центр сцены по Y
    cz = (min(zs) + max(zs)) / 2.0            # центр сцены по Z
    rotated = []                              # повёрнутые вершины по многоугольникам
    for poly in scene["polys"]:               # перебираем многоугольники
        arr = []                              # вершины текущего многоугольника
        for v in poly["verts"]:               # перебираем вершины
            x, y, z = v[0] - cx, v[1] - cy, v[2] - cz     # переносим центр в начало
            arr.append(rotate_point(x, y, z, yaw, pitch)) # поворачиваем камерой
        rotated.append((poly, arr))           # запоминаем результат
    px = [q[0] for _, arr in rotated for q in arr]       # все X после поворота
    py = [q[1] for _, arr in rotated for q in arr]       # все Y после поворота
    w = max(px) - min(px)                     # ширина проекции
    h = max(py) - min(py)                     # высота проекции
    scale = min((SCREEN - 3.0) / max(w, 1e-6), (SCREEN - 3.0) / max(h, 1e-6)) * zoom   # масштаб
    ox = SCREEN / 2 - (min(px) + max(px)) / 2 * scale    # сдвиг по X
    oy = SCREEN / 2 - (min(py) + max(py)) / 2 * scale    # сдвиг по Y
    polys = []                                # многоугольники в координатах растра
    for poly, arr in rotated:                 # перебираем повёрнутые многоугольники
        nv = [(ox + q[0] * scale, oy + q[1] * scale, q[2]) for q in arr]     # в растр
        if area2(nv) < 1e-5:                  # слишком узкая проекция
            continue                          # пропускаем многоугольник
        plane = plane_from_points(nv[0], nv[1], nv[2])        # плоскость после поворота
        norm = math.sqrt(plane[0] ** 2 + plane[1] ** 2 + plane[2] ** 2)   # длина нормали
        if norm < 1e-9 or abs(plane[2]) / norm < 0.02:        # почти вертикальная плоскость
            continue                          # пропускаем многоугольник
        polys.append({"id": poly["id"], "color": poly["color"],
                      "verts": nv, "plane": plane})           # добавляем в сцену
    return {"name": scene["name"], "polys": polys,
            "cam": {"yaw": yaw_deg, "pitch": pitch_deg}}      # сцена глазами камеры


# лёгкая тонировка цвета по ориентации плоскости (объёмный эффект)
def shade_color(hex_color, plane):
    a, b, c, d = plane                       # коэффициенты плоскости
    norm = math.sqrt(a * a + b * b + c * c)  # длина нормали
    k = 0.66 + 0.38 * abs(c) / norm          # чем «фронтальнее» грань, тем светлее
    r = int(int(hex_color[1:3], 16) * k)     # красная составляющая
    g = int(int(hex_color[3:5], 16) * k)     # зелёная составляющая
    b2 = int(int(hex_color[5:7], 16) * k)    # синяя составляющая
    return "#%02x%02x%02x" % (min(255, r), min(255, g), min(255, b2))


# построение всех шагов алгоритма: список событий для пошаговой демонстрации
def build_events(scene):
    t0 = time.perf_counter()                  # замер времени построения событий
    events = []                               # список событий пошаговой работы
    frame = [[0] * SCREEN for _ in range(SCREEN)]      # буфер кадра всего экрана
    zbuf = [[None] * SCREEN for _ in range(SCREEN)]    # z-буфер всего экрана
    linebuf = [[0] * SCREEN for _ in range(SCREEN)]    # буфер видимых пикселов рёбер
    stats = {"fills": {}, "splits": 0, "vis": 0, "hid": 0, "intervals": 0}   # счётчики
    polys = {p["id"]: p for p in scene["polys"]}       # быстрый доступ к многоугольникам
    all_edges = build_edges(scene)            # все рёбра сцены

    def z_of(pid, x, y):                      # глубина многоугольника в точке строки
        return plane_z(polys[pid]["plane"], x, y)       # по уравнению его плоскости

    row_ctx = {"snap": None, "crossings": None}     # снимки АСР и пересечений строки

    def emit(kind, y, text=None, console=None, ael=None, flags=None,
             crossings=None, interval=None, split_x=None, cells=None, line=None):
        ev = {"kind": kind, "y": y, "text": text or [], "console": console,
              "ael": ael if ael is not None else row_ctx["snap"],
              "crossings": crossings if crossings is not None else row_ctx["crossings"],
              "flags": flags, "interval": interval, "split_x": split_x,
              "cells": cells or [], "line": line or []}
        events.append(ev)                     # добавляем событие в общий список
        return ev                             # возвращаем для дополнения

    def do_fill(y, a, b, pid, note):          # закраска полосы [a, b) атрибутом pid
        yc = y + 0.5                          # центр текущей строки
        xs = pixel_span(a, b)                 # пикселы, чьи центры попали в полосу
        cells = []                            # список изменённых ячеек
        for x in xs:                          # по всем пикселам полосы
            if pid == 0:                      # фон: глубину не вычисляем
                continue                      # пикселы фона остаются пустыми
            z = z_of(pid, x + 0.5, yc)        # глубина многоугольника в центре пиксела
            frame[y][x] = pid                 # атрибут в буфер кадра
            zbuf[y][x] = z                    # глубина в z-буфер
            cells.append((x, pid, z))         # запоминаем изменение
            stats["fills"][pid] = stats["fills"].get(pid, 0) + 1         # статистика
        span = "фон" if pid == 0 else "M%d" % pid                        # имя для журнала
        if xs:                                # событие только если что-то закрашено
            lo, hi = xs[0], xs[-1]            # диапазон закрашенных пикселов
            emit("fill", y, interval=(a, b), flags=dict(snapshot_flags),
                 cells=cells, text=["[строка %d] [%.2f..%.2f) -> %s; %s; пикселы %d-%d"
                                    % (y, a, b, span, note, lo, hi)],
                 console="[строка %d] [%.2f..%.2f) -> %s; %s; пикселы %d-%d"
                         % (y, a, b, span, note, lo, hi))    # журнал шага
        return cells                          # возвращаем изменения

    def resolve(y, a, b, actives):            # обработка интервала с несколькими отрезками
        stack = [(a, b)]                      # стек подынтервалов (правые — в стек)
        guard = 0                             # предохранитель от зацикливания
        while stack:                          # пока стек не пуст
            guard += 1                        # считаем итерации
            if guard > 400:                   # аварийный выход из цикла
                break                         # защита от бесконечного разбиения
            ca, cb = stack.pop()              # берём очередной подынтервал
            if cb - ca <= 1e-9:               # пустой по ширине — пропускаем
                continue                      # к следующему
            split = None                      # найденная точка разбиения
            for ii in range(len(actives)):    # перебираем пары отрезков
                for jj in range(ii + 1, len(actives)):
                    p1 = actives[ii]          # номер первого многоугольника пары
                    p2 = actives[jj]          # номер второго многоугольника пары
                    fL = z_of(p1, ca, y + 0.5) - z_of(p2, ca, y + 0.5)    # разность слева
                    fR = z_of(p1, cb, y + 0.5) - z_of(p2, cb, y + 0.5)    # разность справа
                    sL = 0 if abs(fL) < 1e-9 else (1 if fL > 0 else -1)   # знак слева
                    sR = 0 if abs(fR) < 1e-9 else (1 if fR > 0 else -1)   # знак справа
                    if sL * sR < 0:           # знаки разные — отрезки пересекаются
                        xi = ca + (cb - ca) * (fL / (fL - fR))   # абсцисса пересечения
                        if ca + 1e-7 < xi < cb - 1e-7:           # точка внутри интервала
                            split = (xi, p1, p2, fL, fR)         # запоминаем разбиение
                            break             # достаточно одной пары
                if split:                     # разбиение уже найдено
                    break                     # выходим из внешнего цикла
            if split:                         # если нашли пересечение
                xi, p1, p2, fL, fR = split    # распаковываем данные разбиения
                stats["splits"] += 1          # счётчик разбиений
                emit("split", y, interval=(ca, cb), split_x=xi, flags=dict(snapshot_flags),
                     text=["[строка %d] [%.2f..%.2f): у M%d и M%d знаки разностей глубин "
                           "разные (%.2f и %.2f) -> пересечение при x=%.2f, разбиение"
                           % (y, ca, cb, p1, p2, fL, fR, xi)],
                     console="[строка %d] [%.2f..%.2f): M%d/M%d пересекаются при x=%.2f -> "
                             "разбиение" % (y, ca, cb, p1, p2, xi))     # журнал
                stack.append((xi, cb))        # правая часть — в стек
                stack.append((ca, xi))        # левая часть обрабатывается первой
                continue                      # продолжаем со левым подынтервалом
            xm = 0.5 * (ca + cb)              # середина подынтервала
            best = actives[0]                 # лучший по глубине многоугольник
            bz = z_of(best, xm, y + 0.5)      # его глубина в середине
            for pid in actives[1:]:           # сравниваем с остальными активными
                z = z_of(pid, xm, y + 0.5)    # глубина очередного многоугольника
                if z > bz + 1e-12:            # строго ближе к наблюдателю
                    best = pid                # запоминаем нового лидера
                    bz = z                    # и его глубину
            vals = ", ".join("z(M%d)=%.2f" % (p, z_of(p, xm, y + 0.5)) for p in actives)
            do_fill(y, ca, cb, best, "в середине интервала " + vals)     # закраска
        return None                           # завершение обработки интервала

    snapshot_flags = {}                       # текущее состояние флагов (для журнала)

    prev_ael = []                             # рёбра, активные на предыдущей строке
    rows_done = 0                             # число обработанных строк
    for y in range(SCREEN - 1, -1, -1):       # проходим строки сверху вниз
        yc = y + 0.5                          # центр текущей строки
        cur_ael = [e for e in all_edges if not e["horizontal"]
                   and e["last_row"] <= y <= e["first_row"]]     # активные рёбра строки
        for e in cur_ael:                     # обновляем абсциссы и счётчики строк
            e["x_row"] = edge_x_at(e, yc)     # абсцисса пересечения на текущей строке
            e["dy"] = y - e["last_row"] + 1   # сколько строк ещё пересекает ребро
        has_h = any(e["horizontal"] and e["row_h"] == y for e in all_edges)   # горизонтальные
        if not cur_ael and not has_h:         # строка пуста
            continue                          # пропускаем её
        rows_done += 1                        # считаем обработанные строки
        added = [e for e in cur_ael if e not in prev_ael]    # новые рёбра на строке
        removed = [e for e in prev_ael if e not in cur_ael]  # рёбра, покинувшие список
        cur_sorted = sorted(cur_ael, key=lambda t: t["x_row"])       # сортировка по X
        snap = [{"x": e["x_row"], "dx": e["step"], "dy": e["dy"], "pid": e["pid"],
                 "label": e["label"]} for e in cur_sorted]           # снимок для таблицы
        crossings = [(e["x_row"], e["pid"]) for e in cur_sorted]     # точки пересечения
        row_ctx["snap"] = snap                # снимок АСР для всех событий строки
        row_ctx["crossings"] = crossings      # пересечения для всех событий строки
        cross_str = ", ".join("%.2f" % c[0] for c in crossings) if crossings else "нет"
        trow = ["[строка %d] начало: центр строки y=%.1f;" % (y, yc),
                " точки пересечения: " + cross_str]
        emit("row_begin", y, ael=snap, crossings=crossings, text=trow,
             console="[строка %d] начало обработки (центр y=%.1f); пересечения: %s"
                     % (y, yc, cross_str))     # событие начала строки
        if added or removed:                  # состав списка изменился
            emit("ael", y, ael=snap, flags={p: 0 for p in polys}, crossings=crossings,
                 text=["[строка %d] АСР: добавлено рёбер %d, удалено %d; активных рёбер %d"
                       % (y, len(added), len(removed), len(cur_ael))],
                 console="[строка %d] АСР: +%d, -%d; активных рёбер %d"
                         % (y, len(added), len(removed), len(cur_ael)))     # журнал АСР
        else:                                 # состав списка прежний
            emit("ael", y, ael=snap, flags={p: 0 for p in polys}, crossings=crossings,
                 text=["[строка %d] АСР: состав прежний; активных рёбер %d" % (y, len(cur_ael))],
                 console="[строка %d] АСР: активных рёбер %d" % (y, len(cur_ael)))  # журнал
        snapshot_flags = {p: 0 for p in polys}          # флаги в начале строки — нули
        groups = []                           # группировка рёбер с равной абсциссой
        for e in cur_sorted:                  # проходим по отсортированным рёбрам
            if groups and abs(e["x_row"] - groups[-1][0]) < 1e-7:    # абсциссы совпали
                groups[-1][1].append(e)       # добавляем в текущую группу
            else:
                groups.append((e["x_row"], [e]))    # начинаем новую группу
        xcur = 0.0                            # левая граница текущего интервала
        for xg, es in groups:                 # интервалы до каждой группы
            xa = max(xcur, 0.0)               # левая граница с учётом экрана
            xb = min(xg, float(SCREEN))       # правая граница с учётом экрана
            if xb - xa > 1e-9:                # интервал ненулевой ширины
                act = [p for p in sorted(snapshot_flags) if snapshot_flags[p]]   # активные
                stats["intervals"] += 1       # счётчик интервалов
                if not act:                   # активных нет — фон
                    do_fill(y, xa, xb, 0, "активных многоугольников нет")     # фон
                elif len(act) == 1:           # ровно один многоугольник
                    do_fill(y, xa, xb, act[0], "активен один многоугольник M%d" % act[0])
                else:                         # несколько — сравнение глубин
                    resolve(y, xa, xb, act)   # анализ и возможное разбиение
            for e in es:                      # обрабатываем пересечение группы
                snapshot_flags[e["pid"]] ^= 1 # переключаем флаг многоугольника
            xcur = xg                         # сдвигаем левую границу
        xa = max(xcur, 0.0)                   # хвостовой интервал до края экрана
        xb = float(SCREEN)                    # правая граница — край экрана
        if xb - xa > 1e-9 and cur_ael:        # интервал ненулевой ширины при активных рёбрах
            act = [p for p in sorted(snapshot_flags) if snapshot_flags[p]]       # активные
            stats["intervals"] += 1           # счётчик интервалов
            if not act:                       # за последним ребром — фон
                do_fill(y, xa, xb, 0, "активных многоугольников нет")         # фон
            elif len(act) == 1:               # один многоугольник
                do_fill(y, xa, xb, act[0], "активен один многоугольник M%d" % act[0])
            else:                             # несколько — сравнение глубин
                resolve(y, xa, xb, act)       # анализ и возможное разбиение
        line_cells = []                       # видимые пикселы рёбер текущей строки
        endings = []                          # рёбра, заканчивающиеся на этой строке
        for e in cur_ael:                     # проверяем видимость рёбер строки
            xe = e["x_row"]                   # абсцисса пересечения ребра со строкой
            for x in range(SCREEN):           # пикселы, ближайшие к пересечению
                if abs((x + 0.5) - xe) <= 0.5 + 1e-9:    # центр пиксела рядом с ребром
                    if zbuf[y][x] is None:    # грань пиксел не закрывает
                        vis = True            # ребро видно на фоне
                    else:
                        ze = z_of(e["pid"], x + 0.5, yc)     # глубина ребра в центре
                        vis = ze >= zbuf[y][x] - 1e-6        # ребро не глубже видимой грани
                    if vis:                   # ребро в этом пикселе видимо
                        linebuf[y][x] = e["pid"]     # отмечаем видимый пиксел
                        line_cells.append((x, e["pid"]))     # запоминаем изменение
                        stats["vis"] += 1     # счётчик видимых пикселов
                    else:
                        stats["hid"] += 1     # счётчик скрытых пикселов
            if e["last_row"] == y:            # ребро достигло нижней границы
                endings.append(e["label"])    # запоминаем для журнала
        for e in all_edges:                   # горизонтальные рёбра строки
            if e["horizontal"] and e["row_h"] == y:              # ребро принадлежит строке
                for x in range(SCREEN):       # пикселы вдоль ребра
                    if e["lo"] - 0.5 <= x + 0.5 <= e["hi"] + 0.5:    # пиксел на ребре
                        ze = z_of(e["pid"], x + 0.5, e["y"])         # глубина ребра
                        if zbuf[y][x] is None:                       # фон под ребром
                            vis = True        # ребро видно
                        else:
                            vis = ze >= zbuf[y][x] - 1e-6            # сравнение глубин
                        if vis:           # ребро в этом пикселе видимо
                            linebuf[y][x] = e["pid"]     # отмечаем пиксел
                            line_cells.append((x, e["pid"]))         # изменение
                            stats["vis"] += 1            # счётчик видимых
                        else:
                            stats["hid"] += 1            # счётчик скрытых
        fstr = "".join(str(frame[y][x]) for x in range(SCREEN))      # строка буфера кадра
        zs = ["%3s" % ("-" if zbuf[y][x] is None else str(int(math.floor(zbuf[y][x] + 0.5))))
              for x in range(SCREEN)]         # строка z-буфера (округлённые значения)
        zstr = "".join(zs[:16]) + " " + "".join(zs[16:])             # две половины строки
        text = ["[строка %d] завершена; видимых пикселов рёбер %d" % (y, len(line_cells)),
                "буфер кадра: " + fstr, "z-буфер: " + zstr]
        if endings:                           # какие рёбра закончились
            text.append("достигли нижней границы: " + ", ".join(endings))
        emit("row_done", y, ael=snap, flags=dict(snapshot_flags), crossings=crossings,
             line=line_cells, text=text,
             console="[строка %d] завершена; видимых пикселов рёбер %d" % (y, len(line_cells)))
        prev_ael = cur_ael                    # запоминаем активные рёбра для след. строки
    row_ctx["snap"] = None                    # перед итоговым событием снимки сбрасываем
    row_ctx["crossings"] = None               # строки больше не показываются
    used = "%.1f мс" % (1000.0 * (time.perf_counter() - t0))         # время построения
    fcounts = ", ".join("M%d: %d" % (p, stats["fills"].get(p, 0))
                        for p in sorted(polys))  # закрашенные пикселы по многоугольникам
    emit("done", None, text=["[готово] строк обработано %d; интервалов %d; разбиений %d; "
                             "закраска (%s); видимых пикселов рёбер %d; расчёт %s"
                             % (rows_done, stats["intervals"], stats["splits"], fcounts,
                                stats["vis"], used)],
         console="[готово] строк %d; интервалов %d; разбиений %d; закраска (%s); "
                 "видимых пикселов рёбер %d; расчёт %s"
                 % (rows_done, stats["intervals"], stats["splits"], fcounts, stats["vis"], used))
    start = "Сцена: %s; растр %dx%d; обработка строк сверху вниз" % (scene["name"], SCREEN,
                                                                    SCREEN)
    if events:                                # добавляем стартовое сообщение в начало
        events[0]["text"] = [start] + events[0]["text"]      # в первое событие
        events[0]["console"] = start          # дубль в консоль
    return {"events": events, "frame": frame, "zbuf": zbuf, "linebuf": linebuf,
            "stats": stats, "edges": all_edges}               # результат построения


# эталонная закраска: попиксельный перебор без интервалов
def reference_frame(scene):
    frame = [[0] * SCREEN for _ in range(SCREEN)]      # буфер кадра эталона
    zbuf = [[None] * SCREEN for _ in range(SCREEN)]    # z-буфер эталона
    for y in range(SCREEN):                   # все строки растра
        for x in range(SCREEN):               # все пикселы строки
            px, py = x + 0.5, y + 0.5         # центр пиксела
            best = 0                          # лучший атрибут (0 — фон)
            bz = XMIN                         # лучшая глубина
            for poly in scene["polys"]:       # перебираем многоугольники
                if point_in_polygon(px, py, poly["verts"]):      # пиксел внутри проекции
                    z = plane_z(poly["plane"], px, py)           # глубина в пикселе
                    if z > bz + 1e-12:        # строго ближе к наблюдателю
                        bz = z                # новая лучшая глубина
                        best = poly["id"]     # новый атрибут
            frame[y][x] = best                # записываем атрибут
            zbuf[y][x] = bz if best else None # записываем глубину
    return frame, zbuf                        # эталонные буферы


# эталонная видимость рёбер: попиксельное сравнение с глубинами граней
def reference_lines(scene):
    _, rzbuf = reference_frame(scene)         # эталонный z-буфер сцены
    lb = [[0] * SCREEN for _ in range(SCREEN)]         # буфер видимых рёбер эталона
    for e in build_edges(scene):              # перебираем все рёбра сцены
        if e["horizontal"]:                   # горизонтальное ребро
            y = e["row_h"]                    # его строка растра
            for x in range(SCREEN):           # пикселы вдоль ребра
                if e["lo"] - 0.5 <= x + 0.5 <= e["hi"] + 0.5:     # пиксел принадлежит ребру
                    z = plane_z(scene["polys"][e["pid"] - 1]["plane"], x + 0.5, e["y"])
                    if rzbuf[y][x] is None or z >= rzbuf[y][x] - 1e-6:
                        lb[y][x] = e["pid"]   # видимый пиксел
            continue                          # к следующему ребру
        for y in range(max(e["last_row"], 0), min(e["first_row"], SCREEN - 1) + 1):   # строки
            yc = y + 0.5                      # центр строки
            xe = edge_x_at(e, yc)             # абсцисса пересечения
            for x in range(SCREEN):           # пикселы у пересечения
                if abs((x + 0.5) - xe) <= 0.5 + 1e-9:         # центр рядом с ребром
                    z = plane_z(scene["polys"][e["pid"] - 1]["plane"], x + 0.5, yc)
                    if rzbuf[y][x] is None or z >= rzbuf[y][x] - 1e-6:
                        lb[y][x] = e["pid"]   # видимый пиксел
    return lb                                 # эталонный буфер рёбер


# сверка результата с эталоном по буферу кадра и z-буферу
def check_frame(scene, res):
    rframe, rzbuf = reference_frame(scene)    # строим эталон
    bad = 0                                   # число расхождений
    for y in range(SCREEN):                   # сравниваем каждый пиксел
        for x in range(SCREEN):               # по всей строке
            if res["frame"][y][x] != rframe[y][x]:
                bad += 1                      # несовпадение атрибута
            elif rframe[y][x] != 0:           # при совпадении атрибута
                z1 = res["zbuf"][y][x]        # глубина интервального алгоритма
                z2 = rzbuf[y][x]              # глубина эталона
                if z1 is None or abs(z1 - z2) > 1e-6:
                    bad += 1                  # несовпадение глубины
    return bad                                # 0 — полное совпадение


# сверка видимых линий с эталоном
def check_lines(scene, res):
    rlb = reference_lines(scene)              # эталонный буфер рёбер
    bad = 0                                   # число расхождений
    for y in range(SCREEN):                   # сравниваем каждый пиксел
        for x in range(SCREEN):               # по всей строке
            if (res["linebuf"][y][x] != 0) != (rlb[y][x] != 0):
                bad += 1                      # расхождение видимости пиксела
    return bad                                # 0 — полное совпадение


# контрольные значения строки 15 для тестовой сцены
def check_reference_row():
    scene = scene_triangle_vs_rect()          # контрольная сцена
    res = build_events(scene)                 # полное построение событий
    errs = []                                 # список замечаний
    if abs(plane_z(scene["polys"][1]["plane"], 15.5, 15.5) - 14.5) > 1e-9:
        errs.append("глубина треугольника в точке (15.5, 15.5)")     # проверка глубины
    if abs(plane_z(scene["polys"][1]["plane"], 25.5, 15.5) - 7.0) > 1e-9:
        errs.append("глубина треугольника в точке (25.5, 15.5)")     # вторая глубина
    y15 = [e for e in res["events"] if e["kind"] == "split" and e["y"] == 15]    # разбиения
    if not y15 or abs(y15[0]["split_x"] - 21.5) > 1e-9:
        errs.append("точка разбиения интервала на строке 15")        # проверка разбиения
    row = res["frame"][15]                    # строка 15 буфера кадра
    if row[20] != 2 or row[21] != 1 or row[25] != 2 or row[14] != 1:
        errs.append("видимость многоугольников на строке 15")        # проверка видимости
    return errs                               # пусто — все контрольные значения верны


# запуск всех проверок и печать результатов
def run_checks():
    ok = True                                 # общий итог проверок
    scenes = [scene_triangle_vs_rect(), scene_two_triangles(), scene_generated(DEFAULT_SEED)]
    for sc in scenes:                         # проверяем каждую сцену
        res = build_events(sc)                # пошаговое построение
        bf = check_frame(sc, res)             # сверка буферов кадра и z-буфера
        bl = check_lines(sc, res)             # сверка видимых линий
        print("Сцена: %s" % sc["name"])       # имя проверяемой сцены
        print("  сверка с эталонным z-буфером: расхождений %d %s"
              % (bf, "OK" if bf == 0 else "ОШИБКА"))            # результат сверки буферов
        print("  сверка видимых линий: расхождений %d %s"
              % (bl, "OK" if bl == 0 else "ОШИБКА"))            # результат сверки линий
        ok = ok and bf == 0 and bl == 0       # накапливаем итог
    errs = check_reference_row()              # контрольные значения строки 15
    print("  контрольные значения строки 15: %s"
          % ("OK" if not errs else "ОШИБКА: " + "; ".join(errs)))   # печать результата
    ok = ok and not errs                      # учитываем в итоге
    print("ИТОГ: " + ("все проверки пройдены" if ok else "есть расхождения"))   # вердикт
    return ok                                 # возвращаем итог


# приложение: окно, холст, пошаговое управление и отрисовка
class ScanApp:
    # создание интерфейса (mainloop запускается отдельно, в main)
    def __init__(self, root):
        self.root = root                      # главное окно приложения
        self.scenes = []                      # список сцен приложения
        self.scene_index = 0                  # номер текущей сцены
        self.seed = DEFAULT_SEED              # зерно генератора сцены
        self.show_faces = True                # показывать закраску граней
        self.show_lines = True                # показывать видимые линии
        self.auto_on = False                  # автоматический режим выключен
        self.after_id = None                  # идентификатор отложенного шага
        self.cam_yaw = CAM_YAW                # текущий поворот камеры
        self.cam_pitch = CAM_PITCH            # текущий наклон камеры
        self.cam_zoom = CAM_ZOOM              # текущий масштаб камеры
        self.drag_start = None                # точка начала перетаскивания мышью
        self.drag_last = None                 # предыдущая точка мыши
        self.drag_moved = False               # был ли поворот камеры
        self.last_cam_time = 0.0              # время последнего пересчёта вида

        root.title("Удаление невидимых граней и линий: интервальный алгоритм "
                   "построчного сканирования (вариант 5)")    # заголовок окна
        root.geometry("%dx%d" % (WIN_W, WIN_H))               # размер окна
        root.minsize(1180, 800)                               # минимальный размер
        root.configure(bg="#202028")                          # фон окна

        help_text = ("Управление:  → или Enter — шаг;  N — до конца строки;  Пробел — "
                     "выполнить мгновенно;  A — авто/пауза;  0 — сброс\n"
                     "C — сменить сцену;  G — перегенерировать;  V — вид (грани/линии);  "
                     "T — проверка;  H — сброс камеры\n"
                     "Камера: ЛКМ — вращение, колесо — масштаб;  шаг за шагом: АСР, "
                     "интервалы, разбиение, сравнение глубин, z-буфер")
        self.help_label = tk.Label(root, text=help_text, justify="left", anchor="w",
                                   font=("Consolas", 10), bg="#202028", fg="#d0d0d8",
                                   padx=10, pady=6)           # памятка сверху окна
        self.help_label.pack(fill="x")        # памятка на всю ширину

        buttons = tk.Frame(root, bg="#202028")                     # контейнер кнопок
        buttons.pack(fill="x")                # кнопки под памяткой
        self.btn_scene = tk.Button(buttons, text="Сцена (C)", command=self.next_scene,
                                   takefocus=0)                # кнопка смены сцены
        self.btn_scene.pack(side="left", padx=5, pady=4)      # размещение кнопки
        self.btn_instant = tk.Button(buttons, text="Мгновенно (Space)",
                                     command=self.run_instant, takefocus=0)   # всё сразу
        self.btn_instant.pack(side="left", padx=5, pady=4)    # размещение кнопки
        self.btn_auto = tk.Button(buttons, text="Авто (A)", command=self.toggle_auto,
                                  takefocus=0)                 # кнопка авторежима
        self.btn_auto.pack(side="left", padx=5, pady=4)       # размещение кнопки
        self.btn_step = tk.Button(buttons, text="Шаг (→)", command=self.step,
                                  takefocus=0)                 # кнопка одного шага
        self.btn_step.pack(side="left", padx=5, pady=4)       # размещение кнопки
        self.btn_row = tk.Button(buttons, text="До конца строки (N)", command=self.finish_row,
                                 takefocus=0)                  # кнопка шага до конца строки
        self.btn_row.pack(side="left", padx=5, pady=4)        # размещение кнопки
        self.btn_view = tk.Button(buttons, text="Вид (V)", command=self.cycle_view,
                                  takefocus=0)                 # кнопка режима вида
        self.btn_view.pack(side="left", padx=5, pady=4)       # размещение кнопки
        self.btn_check = tk.Button(buttons, text="Проверка (T)", command=self.check_all,
                                   takefocus=0)                # кнопка проверок
        self.btn_check.pack(side="left", padx=5, pady=4)      # размещение кнопки
        self.btn_cam = tk.Button(buttons, text="Камера (H)", command=self.reset_camera,
                                 takefocus=0)                  # кнопка сброса камеры
        self.btn_cam.pack(side="left", padx=5, pady=4)        # размещение кнопки
        self.btn_reset = tk.Button(buttons, text="Сброс (0)", command=self.reset,
                                   takefocus=0)                # кнопка сброса
        self.btn_reset.pack(side="left", padx=5, pady=4)      # размещение кнопки

        self.canvas = tk.Canvas(root, bg=CANVAS_BG, width=CANVAS_W, height=CANVAS_H,
                                highlightthickness=0)          # холст для отрисовки
        self.canvas.pack(fill="both", expand=False)           # размещение холста
        self.font_log = tkfont.Font(root=root, family="Consolas", size=9)     # шрифт журнала
        self.font_small = tkfont.Font(root=root, family="Consolas", size=8)   # мелкий шрифт
        root.bind("<KeyPress>", self.on_key)                  # клавиши обрабатывает окно
        self.canvas.bind("<ButtonPress-1>", self.on_mouse_down)     # ЛКМ — начало вращения
        self.canvas.bind("<B1-Motion>", self.on_mouse_drag)         # ЛКМ тянем — вращаем
        self.canvas.bind("<ButtonRelease-1>", self.on_mouse_up)     # отпускание — шаг/финал
        self.canvas.bind("<MouseWheel>", self.on_mouse_wheel)       # колесо — масштаб
        self.canvas.focus_set()               # фокус — на холст
        self.reload_scene()                   # строим первую сцену и рисуем её

    # список сцен: тест протыкания, второй тест, сгенерированные многоугольники
    def build_scene_list(self):
        return [scene_triangle_vs_rect(),    # тестовая сцена с протыканием
                scene_two_triangles(),       # вторая тестовая сцена с протыканием
                scene_generated(self.seed)]  # сцена сгенерированных многоугольников

    # загрузка текущей сцены: список сцен и построение вида
    def reload_scene(self):
        self.scenes = self.build_scene_list()          # пересобираем список сцен
        self.scene = self.scenes[self.scene_index]     # текущая сцена (исходные координаты)
        self.load_view(0)                     # строим вид и шаги с начала
        self.print_scene()                    # координаты в консоль

    # построение вида камерой и шагов алгоритма; keep — сколько шагов повторить
    def load_view(self, keep=0):
        self.view = camera_scene(self.scene, self.cam_yaw, self.cam_pitch, self.cam_zoom)
        self.view_lookup = {p["id"]: p for p in self.view["polys"]}   # доступ по номеру
        self.res = build_events(self.view)             # все шаги для текущего вида
        self.events = self.res["events"]               # список событий
        self.step_index = 0                   # номер показанного шага
        self.frame = [[0] * SCREEN for _ in range(SCREEN)]      # показываемый буфер кадра
        self.zbuf = [[None] * SCREEN for _ in range(SCREEN)]    # показываемый z-буфер
        self.linebuf = [[0] * SCREEN for _ in range(SCREEN)]    # показываемые линии
        self.cur = None                       # текущее показанное событие
        self.log = ["Сцена: " + self.scene["name"]]    # журнал работы
        self.log.append("Камера: поворот %.0f°, наклон %.0f°, масштаб %.2f"
                        % (self.cam_yaw, self.cam_pitch, self.cam_zoom))
        self.log += self.describe_scene()     # координаты многоугольников в журнал
        if keep > 0:                          # повторяем ранее пройденные шаги
            count = min(keep, len(self.events))     # не больше числа событий
            for ev in self.events[:count]:    # применяем события без отрисовки
                self.apply_event(ev)          # к буферам и журналу
            self.step_index = count           # фиксируем позицию
        self.redraw()                         # отрисовка

    # текстовое описание сцены: многоугольники и координаты вершин
    def describe_scene(self):
        out = []                              # строки описания сцены
        for p in self.scene["polys"]:         # перебираем многоугольники
            vs = ", ".join("(%.1f, %.1f, %.1f)" % v for v in p["verts"])     # координаты
            out.append("M%d (%d вершин): %s" % (p["id"], len(p["verts"]), vs))    # строка
        return out                            # список строк

    # печать координат сцены в консоль
    def print_scene(self):
        print("Сцена: %s" % self.scene["name"])     # имя сцены
        print("Многоугольников: %d" % len(self.scene["polys"]))              # их число
        for line in self.describe_scene():    # перебираем многоугольники
            print("  " + line)                # печатаем строку с координатами

    # применить событие к буферам и журналу
    def apply_event(self, ev):
        for x, pid, z in ev["cells"]:         # применяем закрашенные ячейки
            self.frame[ev["y"]][x] = pid      # атрибут в буфер кадра
            self.zbuf[ev["y"]][x] = z         # глубина в z-буфер
        for x, pid in ev["line"]:             # применяем видимые пикселы рёбер
            self.linebuf[ev["y"]][x] = pid    # отметка видимого пиксела
        self.cur = ev                         # запоминаем текущее событие
        for line in ev["text"]:               # добавляем строки журнала
            self.log.append(line)             # в общий журнал

    # выполнить один шаг: применить очередное событие
    def step(self, draw=True):
        if self.step_index >= len(self.events):      # все шаги уже выполнены
            return False                      # больше нечего показывать
        ev = self.events[self.step_index]     # очередное событие
        self.apply_event(ev)                  # применяем событие
        self.step_index += 1                  # сдвигаем номер шага
        if ev["console"]:                     # дублируем краткую строку в консоль
            print(ev["console"])              # печать текущих параметров
        if draw:                              # если нужна отрисовка
            self.redraw()                     # обновляем картинку
            self.canvas.focus_set()           # возвращаем фокус холсту
        return True                           # шаг сделан

    # выполнить шаги до конца текущей строки
    def finish_row(self, draw=True):
        target = None                         # строка, которую надо завершить
        i = self.step_index                   # просматриваем предстоящие события
        while i < len(self.events):           # ищем ближайшее завершение строки
            ev = self.events[i]               # очередное событие
            if ev["kind"] == "row_done":      # нашли завершение строки
                target = i                    # запоминаем позицию
                break                         # выходим из поиска
            if ev["kind"] == "done":          # сцена закончилась
                target = i                    # завершаем и её
                break                         # выходим из поиска
            i += 1                            # следующий шаг
        if target is None:                    # ничего не нашли
            return                            # выходим
        while self.step_index <= target:      # выполняем шаги до найденной позиции
            if not self.step(draw=False):     # шаг без промежуточной отрисовки
                break                         # события закончились
        if draw:                              # отрисовка после строки
            self.redraw()                     # обновляем картинку
            self.canvas.focus_set()           # фокус холсту

    # мгновенное выполнение: применить все оставшиеся события
    def run_instant(self):
        self.auto_on = False                  # авторежим выключаем
        if self.step_index >= len(self.events):     # всё уже выполнено
            return                            # выходим
        while self.step_index < len(self.events):   # проходим все события
            ev = self.events[self.step_index]       # очередное событие
            self.apply_event(ev)              # применяем без отрисовки
            self.step_index += 1              # сдвигаем номер шага
        if self.cur and self.cur["console"]:  # печатаем итоговую строку
            print(self.cur["console"])        # в консоль
        self.redraw()                         # одна отрисовка в конце
        self.canvas.focus_set()               # фокус холсту

    # автоматический режим: по одной строке за тик
    def toggle_auto(self):
        self.auto_on = not self.auto_on       # переключаем флаг
        if self.auto_on:                      # включаем авто
            self.tick_auto()                  # запускаем цепочку строк
        self.canvas.focus_set()               # возвращаем фокус холсту

    # один тик авторежима: строка целиком и планирование следующего
    def tick_auto(self):
        if not self.auto_on:                  # авторежим выключен
            return                            # ничего не делаем
        self.finish_row(draw=False)           # выполняем очередную строку
        self.redraw()                         # показываем результат строки
        if self.step_index >= len(self.events):     # события закончились
            self.auto_on = False              # выключаем авто
            return                            # выходим
        self.after_id = self.root.after(AUTO_MS, self.tick_auto)     # следующий тик

    # пересчёт вида после изменения камеры (с сохранением пройденных шагов)
    def update_camera(self):
        done = self.step_index >= len(self.events)     # всё уже выполнено
        keep = 10 ** 9 if done else self.step_index    # сколько шагов повторить
        self.load_view(keep)                  # новый вид и повтор шагов
        self.canvas.focus_set()               # фокус холсту

    # сброс камеры в исходное положение
    def reset_camera(self):
        self.cam_yaw = CAM_YAW                # исходный поворот
        self.cam_pitch = CAM_PITCH            # исходный наклон
        self.cam_zoom = CAM_ZOOM              # исходный масштаб
        self.update_camera()                  # пересчёт вида
        self.canvas.focus_set()               # фокус холсту

    # нажатие кнопки мыши: запоминаем начало перетаскивания
    def on_mouse_down(self, event):
        self.drag_start = (event.x, event.y)  # точка нажатия
        self.drag_last = (event.x, event.y)   # предыдущая точка
        self.drag_moved = False               # поворот ещё не начат

    # перетаскивание мышью: вращение камеры
    def on_mouse_drag(self, event):
        if self.drag_last is None:            # кнопка не была нажата
            return                            # выходим
        dx = event.x - self.drag_last[0]      # смещение по горизонтали
        dy = event.y - self.drag_last[1]      # смещение по вертикали
        if abs(event.x - self.drag_start[0]) + abs(event.y - self.drag_start[1]) > 3:
            self.drag_moved = True            # это уже вращение, а не щелчок
        self.drag_last = (event.x, event.y)   # запоминаем точку
        if not self.drag_moved:               # движения пока нет
            return                            # выходим
        self.cam_yaw += dx * CAM_YAW_STEP     # поворот камеры
        self.cam_pitch += dy * CAM_PITCH_STEP # наклон камеры
        self.cam_pitch = max(-CAM_PITCH_LIMIT, min(CAM_PITCH_LIMIT, self.cam_pitch))
        now = time.perf_counter()             # текущее время
        if now - self.last_cam_time < 0.07:   # слишком частые пересчёты
            return                            # пропускаем промежуточный кадр
        self.last_cam_time = now              # запоминаем время
        self.update_camera()                  # пересчитываем вид

    # отпускание кнопки мыши: щелчок без движения — шаг
    def on_mouse_up(self, event):
        if not self.drag_moved:               # движения не было
            self.step()                       # один шаг алгоритма
        else:                                 # был поворот камеры
            self.update_camera()              # финальный пересчёт вида
        self.drag_last = None                 # сбрасываем состояние мыши

    # колесо мыши: масштаб камеры
    def on_mouse_wheel(self, event):
        if event.delta > 0:                   # прокрутка вверх — приблизить
            self.cam_zoom *= 1.06             # увеличиваем масштаб
        else:                                 # прокрутка вниз — отдалить
            self.cam_zoom /= 1.06             # уменьшаем масштаб
        self.cam_zoom = max(0.6, min(1.8, self.cam_zoom))    # ограничиваем масштаб
        self.update_camera()                  # пересчёт вида
        self.canvas.focus_set()               # фокус холсту

    # смена сцены по кругу
    def next_scene(self):
        self.auto_on = False                  # выключаем авторежим
        self.scene_index = (self.scene_index + 1) % len(self.scenes)    # следующая сцена
        self.reload_scene()                   # загружаем её
        self.canvas.focus_set()               # фокус холсту

    # перегенерация сцены многоугольников
    def regenerate(self):
        self.auto_on = False                  # выключаем авторежим
        self.seed += 1                        # новое зерно генератора
        self.scene_index = 2                  # к сцене сгенерированных многоугольников
        self.reload_scene()                   # перестроение сцены
        self.canvas.focus_set()               # фокус холсту

    # сброс к началу текущей сцены
    def reset(self):
        self.auto_on = False                  # выключаем авторежим
        self.step_index = 0                   # к первому шагу
        self.frame = [[0] * SCREEN for _ in range(SCREEN)]      # чистый буфер кадра
        self.zbuf = [[None] * SCREEN for _ in range(SCREEN)]    # чистый z-буфер
        self.linebuf = [[0] * SCREEN for _ in range(SCREEN)]    # чистые линии
        self.cur = None                       # текущего события нет
        self.log = ["Сцена: " + self.scene["name"]]     # журнал сначала
        self.log.append("Камера: поворот %.0f°, наклон %.0f°, масштаб %.2f"
                        % (self.cam_yaw, self.cam_pitch, self.cam_zoom))
        self.log += self.describe_scene()     # с координатами вершин
        self.redraw()                         # отрисовка
        self.canvas.focus_set()               # фокус холсту

    # переключение вида: грани и линии, только грани, только линии
    def cycle_view(self):
        if self.show_faces and self.show_lines:          # было «всё»
            self.show_faces, self.show_lines = True, False    # остаются грани
        elif self.show_faces:                 # было «только грани»
            self.show_faces, self.show_lines = False, True    # остаются линии
        else:                                 # было «только линии»
            self.show_faces, self.show_lines = True, True     # снова всё
        self.redraw()                         # перерисовка
        self.canvas.focus_set()               # фокус холсту

    # запуск проверок по всем сценам
    def check_all(self):
        print("Проверка результата: по всем сценам")     # заголовок в консоль
        ok = run_checks()                     # запускаем сверку с эталоном
        msg = ("Проверка: результат совпадает с эталонным z-буфером и видимыми линиями"
               if ok else "Проверка: обнаружены расхождения — см. консоль")     # итог
        self.log.append(msg)                  # строка в журнал
        self.redraw()                         # обновление картинки
        self.canvas.focus_set()               # фокус холсту

    # обработка нажатия клавиши
    def on_key(self, event):
        k = event.keysym                      # имя клавиши
        if k in ("Right", "Return", "KP_Enter"):     # шаг вперёд
            self.step()                       # один шаг
        elif k in ("n", "N", "т", "Т"):       # до конца строки
            self.finish_row()                 # завершаем строку
        elif k == "space":                    # пробел
            self.run_instant()                # мгновенное выполнение
        elif k in ("a", "A", "ф", "Ф"):       # авторежим
            self.toggle_auto()                # авто/пауза
        elif k in ("c", "C", "с", "С"):       # смена сцены
            self.next_scene()                 # следующая сцена
        elif k in ("g", "G", "п", "П"):       # перегенерация
            self.regenerate()                 # новые многоугольники
        elif k in ("v", "V", "м", "М"):       # вид
            self.cycle_view()                 # переключение вида
        elif k in ("t", "T", "е", "Е"):       # проверка
            self.check_all()                  # сверка с эталоном
        elif k in ("h", "H", "р", "Р"):       # камера
            self.reset_camera()               # сброс камеры
        elif k in ("0",):                     # сброс
            self.reset()                      # к началу сцены

    # перерисовка всей сцены и панелей
    def redraw(self):
        c = self.canvas                       # холст для рисования
        c.delete("all")                       # стираем предыдущий кадр
        self.draw_scene(c)                    # область сцены с закраской и линиями
        self.draw_zbuffer(c)                  # панель z-буфера
        self.draw_ael(c)                      # таблица активных рёбер
        self.draw_log(c)                      # журнал хода выполнения
        self.draw_verts(c)                    # координаты вершин многоугольников
        c.create_text(SCENE_X, 24, anchor="w", text="Проекция сцены камерой "
                      "(растр %dx%d)" % (SCREEN, SCREEN), fill=TITLE_COLOR,
                      font=("Consolas", 11, "bold"))          # заголовок сцены
        mode = ("грани и линии" if self.show_faces and self.show_lines
                else ("только грани" if self.show_faces else "только линии"))  # имя вида
        prog = "шаг %d из %d" % (self.step_index, len(self.events))            # прогресс
        c.create_text(CANVAS_W - 20, 24, anchor="e", text="вид: " + mode + " · " + prog,
                      fill=MUTED_COLOR, font=("Consolas", 10))     # строка состояния справа
        hint = ("→/Enter — шаг;  N — до конца строки;  Space — мгновенно;  A — авто;  "
                "C — сцена;  G — перегенерировать;  V — вид;  T — проверка;  H — камера;  "
                "0 — сброс")
        c.create_text(SCENE_X, CANVAS_H - 16, anchor="w", text=hint,
                      fill=MUTED_COLOR, font=("Consolas", 9))      # подсказка внизу

    # координата X пиксела растра на холсте
    def sx(self, wx):
        return SCENE_X + wx * SCENE_CELL      # линейное преобразование X

    # координата Y пиксела растра на холсте (ось Y растра направлена вверх)
    def sy(self, wy):
        return SCENE_Y + (SCREEN - wy) * SCENE_CELL     # переворот вертикальной оси

    # перенос текста по словам с учётом ширины строки в пикселах
    def wrap_text(self, s, font, width):
        lines = []                            # готовые строки
        cur = ""                             # текущая собираемая строка
        for word in s.split(" "):             # разбираем текст на слова
            t = word if not cur else cur + " " + word    # пробуем добавить слово
            if font.measure(t) <= width:      # слово ещё помещается в строку
                cur = t                       # оставляем его в строке
            else:                             # слово не помещается
                if cur:                       # если строка не пуста
                    lines.append(cur)         # фиксируем её
                cur = word                    # слово переходит на следующую строку
        if cur:                               # остаток текста
            lines.append(cur)                 # добавляем последней строкой
        return lines                          # список готовых строк

    # отрисовка области сцены: закраска, линии, скан-строка, интервал
    def draw_scene(self, c):
        c.create_rectangle(SCENE_X - 1, SCENE_Y - 1, SCENE_X + SCREEN * SCENE_CELL + 1,
                           SCENE_Y + SCREEN * SCENE_CELL + 1, outline="#303040",
                           width=1)           # рамка области сцены
        if self.show_faces:                   # если включена закраска граней
            for y in range(SCREEN):           # по всем строкам растра
                for x in range(SCREEN):       # по всем пикселам
                    pid = self.frame[y][x]    # атрибут пиксела
                    if pid:                   # закрашенный пиксел
                        base = self.scene["polys"][pid - 1]["color"]     # базовый цвет
                        pol = self.view_lookup.get(pid)                  # грань после камеры
                        col = shade_color(base, pol["plane"]) if pol else base   # тонировка
                        c.create_rectangle(self.sx(x), self.sy(y + 1),
                                           self.sx(x + 1), self.sy(y),
                                           fill=col, outline=col)         # квадрат цвета
        for e in self.res["edges"]:           # рёбра сцены (тусклые линии)
            if e["horizontal"]:               # горизонтальное ребро
                x1, x2 = e["lo"], e["hi"]     # пределы по X
                y1 = y2 = e["y"]              # высота ребра
                c.create_line(self.sx(x1), self.sy(y1), self.sx(x2), self.sy(y2),
                              fill=EDGE_DIM, width=1)                 # линия ребра
            else:
                t, b = e["top"], e["bot"]     # концы ребра
                c.create_line(self.sx(t[0]), self.sy(t[1]), self.sx(b[0]), self.sy(b[1]),
                              fill=EDGE_DIM, width=1)                 # линия ребра
        if self.cur and self.cur["ael"]:      # подсветка рёбер из списка активных
            active = set((e["pid"], e["label"]) for e in self.cur["ael"])   # ключи рёбер
            for e in self.res["edges"]:       # перебираем рёбра сцены
                if (e["pid"], e["label"]) not in active:
                    continue                  # ребро не в списке — пропускаем
                if e["horizontal"]:           # горизонтальное ребро
                    x1, x2 = e["lo"], e["hi"]     # пределы по X
                    y1 = y2 = e["y"]              # высота ребра
                    c.create_line(self.sx(x1), self.sy(y1), self.sx(x2), self.sy(y2),
                                  fill=EDGE_ACTIVE, width=2)          # активное ребро
                else:
                    t, b = e["top"], e["bot"]     # концы ребра
                    c.create_line(self.sx(t[0]), self.sy(t[1]), self.sx(b[0]), self.sy(b[1]),
                                  fill=EDGE_ACTIVE, width=2)          # активное ребро
        if self.show_lines:                   # если включён показ линий
            for y in range(SCREEN):           # по всем строкам
                for x in range(SCREEN):       # по всем пикселам
                    if self.linebuf[y][x]:    # видимый пиксел ребра
                        cx, cy = self.sx(x + 0.5), self.sy(y + 0.5)       # центр пиксела
                        r = SCENE_CELL * 0.28     # половина размера маркера
                        c.create_rectangle(cx - r, cy - r, cx + r, cy + r,
                                           fill=EDGE_VISIBLE, outline="")  # маркер линии
        self.draw_axes(c)                     # триада осей под подсветкой строки
        if self.cur and self.cur["y"] is not None:       # есть текущая строка
            y = self.cur["y"]                 # номер строки
            top = self.sy(y + 1)              # верх полосы строки
            bot = self.sy(y)                  # низ полосы строки
            c.create_rectangle(SCENE_X, top, SCENE_X + SCREEN * SCENE_CELL, bot,
                               outline=SCANLINE_COLOR, width=2)     # полоса скан-строки
            for ex, pid in (self.cur["crossings"] or []):           # точки пересечения
                cx, cy = self.sx(ex), self.sy(y + 0.5)              # центр строки
                c.create_oval(cx - 3, cy - 3, cx + 3, cy + 3,
                              fill=CROSS_COLOR, outline="")         # маркер пересечения
            iv = self.cur["interval"]     # текущий интервал
            if iv:                        # если интервал есть
                c.create_rectangle(self.sx(iv[0]), top, self.sx(iv[1]), bot,
                                   fill=INTERVAL_COLOR, stipple="gray25", outline="")   # подсветка
            if self.cur.get("split_x") is not None:      # точка разбиения
                xs = self.sx(self.cur["split_x"])        # абсцисса на холсте
                c.create_line(xs, top - 4, xs, bot + 4, fill=SPLIT_COLOR, width=2,
                              dash=(4, 3))               # штриховая вертикаль разбиения
        kind_names = {"row_begin": "начало строки", "ael": "обновление списка",
                      "fill": "закраска интервала", "split": "разбиение интервала",
                      "row_done": "строка завершена", "done": "обработка завершена"}
        sub = "Строка y=%s" % (self.cur["y"] if self.cur and self.cur["y"] is not None
                               else "-")      # подпись текущей строки
        if self.cur:                          # добавляем текущий шаг алгоритма
            edges = len(self.cur["ael"]) if self.cur["ael"] else 0       # число рёбер в АСР
            sub += "   ·   рёбер: %d   ·   шаг: %s" % (
                edges, kind_names.get(self.cur["kind"], self.cur["kind"]))
        c.create_text(SCENE_X, SCENE_Y + SCREEN * SCENE_CELL + 16, anchor="w", text=sub,
                      fill=TEXT_COLOR, font=("Consolas", 10))     # подпись под сценой
        cam = ("Камера: поворот %.0f°, наклон %.0f°, масштаб %.2f   ·   ЛКМ — вращение, "
               "колесо — масштаб" % (self.cam_yaw, self.cam_pitch, self.cam_zoom))
        c.create_text(SCENE_X, SCENE_Y + SCREEN * SCENE_CELL + 32, anchor="w", text=cam,
                      fill=MUTED_COLOR, font=("Consolas", 9))     # строка камеры
        leg = ("Обозначения: жёлтая полоса — текущая строка; красные точки — пересечения "
               "строки с рёбрами; зелёная подсветка — обрабатываемый интервал; красный "
               "штрих — точка разбиения; светлые маркеры — видимые пикселы рёбер; "
               "триада в левом нижнем углу — оси X, Y, Z")
        ly = SCENE_Y + SCREEN * SCENE_CELL + 52     # верх блока обозначений
        leg_lines = self.wrap_text(leg, self.font_log, 460)     # строки обозначений
        for j, line in enumerate(leg_lines):          # печать строк обозначений
            c.create_text(SCENE_X, ly + j * 14, anchor="nw", text=line, fill=MUTED_COLOR,
                          font=("Consolas", 9))       # строка обозначений
        chip_y = ly + len(leg_lines) * 14 + 4         # ряд цветовых меток под легендой
        for i, p in enumerate(self.scene["polys"]):     # перебираем многоугольники
            cx = SCENE_X + i * 74             # позиция метки по горизонтали
            c.create_rectangle(cx, chip_y, cx + 12, chip_y + 12, fill=p["color"],
                               outline="")    # цветной квадрат многоугольника
            c.create_text(cx + 17, chip_y + 6, anchor="w", text="M%d" % p["id"],
                          fill=TEXT_COLOR, font=("Consolas", 9))     # номер многоугольника

    # отрисовка триады осей: вращается вместе со сценой
    def draw_axes(self, c):
        bx = SCENE_X + AXIS_BOX + 6           # центр площадки по X
        by = SCENE_Y + SCREEN * SCENE_CELL - AXIS_BOX - 6    # центр площадки по Y
        c.create_rectangle(bx - AXIS_BOX, by - AXIS_BOX, bx + AXIS_BOX, by + AXIS_BOX,
                           fill="#171722", outline="#3a3a52")     # подложка триады
        yaw = math.radians(self.cam_yaw)       # текущий поворот камеры
        pitch = math.radians(self.cam_pitch)   # текущий наклон камеры
        axes = [(1.0, 0.0, 0.0, AXIS_COLOR_X, "X"),     # ось X
                (0.0, 1.0, 0.0, AXIS_COLOR_Y, "Y"),     # ось Y
                (0.0, 0.0, 1.0, AXIS_COLOR_Z, "Z")]     # ось Z
        for ux, uy, uz, col, name in axes:      # рисуем три оси по очереди
            rx, ry, rz = rotate_point(ux, uy, uz, yaw, pitch)   # направление оси после камеры
            ex = bx + rx * AXIS_LEN            # конец стрелки по X
            ey = by - ry * AXIS_LEN            # конец стрелки по Y
            c.create_line(bx, by, ex, ey, fill=col, width=2, arrow="last",
                          arrowshape=(7, 8, 3))          # стрелка оси
            ln = math.hypot(rx, ry)            # длина проекции оси на экран
            if ln > 1e-6:                      # ось не вырождена в точку
                lx, ly = rx / ln * 9, -ry / ln * 9       # смещение подписи
            else:                              # ось направлена на наблюдателя
                lx, ly = 0, -12                # подпись ставим сверху
            c.create_text(ex + lx, ey + ly, text=name, fill=col,
                          font=("Consolas", 9, "bold"))       # подпись оси
        c.create_oval(bx - 2, by - 2, bx + 2, by + 2,
                      fill=TEXT_COLOR, outline="")            # начало координат
        c.create_text(bx + 8, by + 10, text="O", fill=MUTED_COLOR,
                      font=("Consolas", 9))                  # метка начала координат

    # отрисовка панели z-буфера: цвет глубины и текущая строка
    def draw_zbuffer(self, c):
        c.create_text(ZBUF_X, 24, anchor="w", text="Z-буфер (цвет — глубина)",
                      fill=TITLE_COLOR, font=("Consolas", 11, "bold"))     # заголовок
        zmin, zmax = self.scene_z_range()     # диапазон глубин сцены
        for y in range(SCREEN):               # по всем строкам
            for x in range(SCREEN):           # по всем пикселам
                x0 = ZBUF_X + x * ZBUF_CELL   # левый край ячейки
                y0 = ZBUF_Y + (SCREEN - 1 - y) * ZBUF_CELL   # верхний край ячейки
                z = self.zbuf[y][x]           # глубина ячейки (или None)
                if z is None:                 # нет данных
                    col = "#161620"           # тёмная ячейка
                else:
                    col = z_color(z, zmin, zmax)     # цвет по глубине
                c.create_rectangle(x0, y0, x0 + ZBUF_CELL, y0 + ZBUF_CELL,
                                   fill=col, outline="#20202c")     # ячейка z-буфера
        if self.cur and self.cur["y"] is not None:       # рамка текущей строки
            y = self.cur["y"]                 # номер строки
            y0 = ZBUF_Y + (SCREEN - 1 - y) * ZBUF_CELL   # верхний край строки сетки
            c.create_rectangle(ZBUF_X - 1, y0 - 1, ZBUF_X + SCREEN * ZBUF_CELL + 1,
                               y0 + ZBUF_CELL + 1, outline=SCANLINE_COLOR, width=2)  # рамка
            zs = ["%2s" % ("-" if self.zbuf[y][x] is None
                           else "%d" % int(math.floor(self.zbuf[y][x] + 0.5)))
                  for x in range(SCREEN)]     # значения z строки по пикселам
            pref = "z, строка %d: " % y       # префикс строки значений
            line1 = pref + "".join(zs[:16])     # первая половина значений
            line2 = " " * len(pref) + "".join(zs[16:])   # вторая половина под тем же отступом
            fs = "".join(str(self.frame[y][x]) for x in range(SCREEN))    # буфер кадра
            sy0 = ZBUF_Y + SCREEN * ZBUF_CELL     # нижний край сетки z-буфера
            c.create_text(ZBUF_X, sy0 + 16, anchor="w", text=line1, fill=TEXT_COLOR,
                          font=("Consolas", 8))            # значения z первой половины
            c.create_text(ZBUF_X, sy0 + 32, anchor="w", text=line2, fill=TEXT_COLOR,
                          font=("Consolas", 8))            # значения z второй половины
            c.create_text(ZBUF_X, sy0 + 54, anchor="w",
                          text="кадр, строка %d: %s" % (y, fs), fill=TEXT_COLOR,
                          font=("Consolas", 8))            # строка буфера кадра

    # диапазон глубин сцены для окраски z-буфера
    def scene_z_range(self):
        zs = [v[2] for p in self.view["polys"] for v in p["verts"]]     # глубины вида
        zmin = min(zs) if zs else 0.0         # минимум глубин
        zmax = max(zs) if zs else 1.0         # максимум глубин
        if zmax - zmin < 1e-9:                # вырожденный диапазон
            zmax = zmin + 1.0                 # расширяем для окраски
        return zmin, zmax                     # возвращаем границы

    # отрисовка таблицы активных рёбер
    def draw_ael(self, c):
        c.create_text(AEL_X, AEL_Y - 24, anchor="w", text="Список активных рёбер (АСР)",
                      fill=TITLE_COLOR, font=("Consolas", 11, "bold"))     # заголовок
        heads = ["x", "dx", "dy", "M", "ребро", "флаг"]  # заголовки столбцов
        colw = [58, 58, 40, 34, 96, 50]       # ширины столбцов
        xoff = 0                              # смещение столбца
        for i, h in enumerate(heads):         # печать заголовков
            c.create_text(AEL_X + xoff, AEL_Y - 6, anchor="w", text=h, fill=MUTED_COLOR,
                          font=("Consolas", 9, "bold"))    # заголовок столбца
            xoff += colw[i]                   # сдвиг к следующему столбцу
        ael = self.cur["ael"] if self.cur else None      # снимок списка из события
        flags = self.cur["flags"] if self.cur else None  # флаги многоугольников
        if not ael:                           # список пуст или не показан
            c.create_text(AEL_X, AEL_Y + 12, anchor="w", text="(нет активных рёбер)",
                          fill=MUTED_COLOR, font=("Consolas", 9))     # пояснение
            return                            # таблица заполнена
        if ael is not None:                   # список есть
            for i, e in enumerate(ael[:10]):  # не более десяти строк таблицы
                yy = AEL_Y + 12 + i * 16      # вертикальная позиция строки
                fl = (flags or {}).get(e["pid"], 0)          # флаг многоугольника
                if fl:                        # активный многоугольник
                    c.create_rectangle(AEL_X - 4, yy - 7, AEL_X + sum(colw), yy + 7,
                                       fill="#243528", outline="")   # подсветка строки
                vals = ["%.2f" % e["x"], "%.2f" % e["dx"], str(e["dy"]),
                        "M%d" % e["pid"], e["label"], "1" if fl else "0"]     # значения
                xoff = 0                  # смещение столбца
                for j, v in enumerate(vals):      # печать значений строки
                    col = TEXT_COLOR if fl else MUTED_COLOR   # цвет текста
                    c.create_text(AEL_X + xoff, yy, anchor="w", text=v, fill=col,
                                  font=("Consolas", 9))     # значение столбца
                    xoff += colw[j]       # сдвиг к следующему столбцу
            if len(ael) > 10:                 # список длиннее показанного
                c.create_text(AEL_X, AEL_Y + 12 + 10 * 16, anchor="w",
                              text="... и ещё рёбер: %d" % (len(ael) - 10),
                              fill=MUTED_COLOR, font=("Consolas", 9))     # примечание

    # отрисовка журнала хода выполнения
    def draw_log(self, c):
        c.create_text(LOG_X, 24, anchor="w", text="Ход выполнения", fill=TITLE_COLOR,
                      font=("Consolas", 11, "bold"))    # заголовок журнала
        lines = []                            # накопленные строки журнала
        for s in self.log:                    # перебираем записи журнала
            for part in self.wrap_text(s, self.font_log, CANVAS_W - LOG_X - 18):
                lines.append(part)            # строка после переноса по ширине
        for i, s in enumerate(lines[-LOG_LINES:]):       # последние строки
            col = TEXT_COLOR                  # цвет строки
            if s.startswith("["):             # строки шагов алгоритма
                col = "#c8c8d8"               # светло-серые
            if "Проверка" in s:               # строка результата проверки
                col = "#69f0ae"               # зелёная
            c.create_text(LOG_X, LOG_Y - 6 + i * 15, anchor="nw", text=s, fill=col,
                          font=("Consolas", 9))     # строка журнала

    # отрисовка координат вершин многоугольников
    def draw_verts(self, c):
        c.create_text(VERT_X, VERT_Y - 20, anchor="w", text="Многоугольники и координаты "
                      "вершин (x, y, z)", fill=TITLE_COLOR,
                      font=("Consolas", 11, "bold"))    # заголовок блока
        yy = VERT_Y                           # текущая вертикальная позиция
        for p in self.scene["polys"]:         # перебираем многоугольники
            text = "M%d (%d вершин): " % (p["id"], len(p["verts"]))          # заголовок
            text += " ".join("(%.1f,\u00A0%.1f,\u00A0%.1f)" % v for v in p["verts"])   # координаты
            for line in self.wrap_text(text, self.font_small, 386):   # перенос строк
                c.create_text(VERT_X, yy, anchor="nw", text=line, fill=p["color"],
                              font=("Consolas", 8))         # строка координат вершин
                yy += 13                      # шаг строки с запасом по высоте
            yy += 6                           # отступ между многоугольниками


# цвет для глубины z: от тёмно-синего (далеко) к ярко-оранжевому (близко)
def z_color(z, zmin, zmax):
    t = (z - zmin) / (zmax - zmin)            # нормированная глубина 0..1
    t = min(max(t, 0.0), 1.0)                 # ограничение диапазона
    r = int(30 + t * (255 - 30))              # красная составляющая
    g = int(42 + t * (112 - 42))              # зелёная составляющая
    b = int(74 + t * (67 - 74))               # синяя составляющая
    return "#%02x%02x%02x" % (r, g, b)        # цвет в шестнадцатеричном виде


# точка входа программы
def main():
    root = tk.Tk()                            # создаём главное окно
    app = ScanApp(root)                       # собираем интерфейс приложения
    app.canvas.focus_set()                    # фокус — на холст, чтобы работали клавиши
    root.mainloop()                           # запускаем цикл обработки событий


if __name__ == "__main__":                    # файл можно импортировать без запуска окна
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        run_checks()                          # проверки без открытия окна
    else:
        main()                                # запускаем программу
