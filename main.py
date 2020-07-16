from pysat.solvers import Solver
import copy
import time

"""
This program solves a sudoku puzzle using reduction to SAT.
Implementation also provides a method for a classical backtracking CSP solution with DFS.
"""


class Sudoku:
    GRID_LEN = 9
    SUBGRID_LEN = 3
    MAX_NUMBER = 9

    def __init__(self, grid, timer=False):
        if len(grid) != self.GRID_LEN:
            raise ValueError('Wrong grid size')
        for row in grid:
            if len(row) != self.GRID_LEN:
                raise ValueError('Wrong grid size')

        self.__grid = grid

        self.__atom_id = {}
        self.__id_atom = {}

        self.__solution = None
        self.__solution_found = False

        self.__timer = timer
        self.__t = 0.1

    def __atom(self, row, col, number):
        """Encode the sudoku cell state to an atom.

        Args:
            a unique triple (<row>, <column>, <assigned number>).
        Returns:
            the number representing atom id.
        """

        if (row, col, number) in self.__atom_id.keys():
            return self.__atom_id[(row, col, number)]
        else:
            self.__id_atom[len(self.__atom_id) + 1] = (row, col, number)
            self.__atom_id[(row, col, number)] = len(self.__atom_id) + 1
            return self.__atom_id[(row, col, number)]

    def __literal(self, x, y, number, negation=False):
        """Make a formula literal

        Args:
            a triple representing atom and negation parameter.
        Returns:
            the number representing literal.
        """
        return int(("-" if negation else "") + str(self.__atom(x, y, number)))

    def solve_as_sat(self):
        """Encode sudoku to a formula and solve as an instance of SAT problem.

        Returns:
            a solved sudoku.
        """

        if self.__timer:
            t_start = time.time()

        self.__solution = None
        self.__solution_found = False

        solver = Solver(name='g3')  # Glucose3

        # constraints given by the initial state:
        for row in range(self.GRID_LEN):
            for col in range(self.GRID_LEN):
                solver.add_clause([self.__literal(row, col, self.__grid[row][col])])

        # there is at least one number in each cell:
        for row in range(self.GRID_LEN):
            for col in range(self.GRID_LEN):
                clause = []
                for number in range(1, self.MAX_NUMBER + 1):
                    clause.append(self.__literal(row, col, number))
                solver.add_clause(clause)

        # all numbers in each row are different:
        for row in range(self.GRID_LEN):
            for colA in range(self.GRID_LEN):
                for colB in range(colA + 1, self.GRID_LEN):
                    for number in range(1, self.MAX_NUMBER + 1):
                        solver.add_clause([self.__literal(row, colA, number, negation=True),
                                           self.__literal(row, colB, number, negation=True)])

        # all numbers in each column are different:
        for col in range(self.GRID_LEN):
            for rowA in range(self.GRID_LEN):
                for rowB in range(rowA + 1, self.GRID_LEN):
                    for number in range(1, self.MAX_NUMBER + 1):
                        solver.add_clause([self.__literal(rowA, col, number, negation=True),
                                           self.__literal(rowB, col, number, negation=True)])

        # all numbers in each sub-grid are different:
        for rowS in range(0, self.GRID_LEN, self.SUBGRID_LEN):
            for colS in range(0, self.GRID_LEN, self.SUBGRID_LEN):
                for rowA in range(rowS, rowS + self.SUBGRID_LEN):
                    for colA in range(colS, colS + self.SUBGRID_LEN):
                        for rowB in range(rowS, rowS + self.SUBGRID_LEN):
                            for colB in range(colS, colS + self.SUBGRID_LEN):
                                if rowB > rowA or (rowB == rowA and colB > colA):
                                    for number in range(1, self.MAX_NUMBER + 1):
                                        solver.add_clause([self.__literal(rowA, colA, number, negation=True),
                                                           self.__literal(rowB, colB, number, negation=True)])

        if not solver.solve():
            return None

        self.__solution_found = True
        self.__solution = copy.deepcopy(self.__grid)
        model = solver.get_model()
        for value in model:
            if value > 0:
                row, col, number = self.__id_atom[value]
                self.__solution[row][col] = number

        if self.__timer:
            self.__t = time.time() - t_start

        return self.__solution

    def __check_constraints(self, grid):
        numbers = set()

        # all numbers in each row are different:
        for row in grid:
            numbers.clear()
            numbers_count = 0
            for entry in row:
                if entry != 0:
                    numbers.add(entry)
                    numbers_count += 1
            if numbers_count != len(numbers):
                return False

        # all numbers in each column are different:
        for col in range(self.GRID_LEN):
            numbers.clear()
            numbers_count = 0
            for row in grid:
                if row[col] != 0:
                    numbers.add(row[col])
                    numbers_count += 1
            if numbers_count != len(numbers):
                return False

        # all numbers in each sub-grid are different:
        for rowS in range(0, self.GRID_LEN, self.SUBGRID_LEN):
            for colS in range(0, self.GRID_LEN, self.SUBGRID_LEN):
                numbers.clear()
                numbers_count = 0
                for row in range(rowS, rowS + self.SUBGRID_LEN):
                    for col in range(colS, colS + self.SUBGRID_LEN):
                        if grid[row][col] != 0:
                            numbers.add(grid[row][col])
                            numbers_count += 1
                if numbers_count != len(numbers):
                    return False

        return True

    def __csp_search(self, grid, row, col):
        if self.__solution_found:
            return

        if not self.__check_constraints(grid):
            return

        if row == self.GRID_LEN:
            self.__solution_found = True
            self.__solution = grid
            return

        if self.__grid[row][col] != 0:
            if col == self.GRID_LEN - 1:
                self.__csp_search(grid, row + 1, 0)
            else:
                self.__csp_search(grid, row, col + 1)
            return

        for number in range(1, self.MAX_NUMBER + 1):
            candidate = copy.deepcopy(grid)
            candidate[row][col] = number
            if col == self.GRID_LEN - 1:
                self.__csp_search(candidate, row + 1, 0)
            else:
                self.__csp_search(candidate, row, col + 1)

    def solve_as_csp(self):
        if self.__timer:
            t_start = time.time()

        self.__solution = None
        self.__solution_found = False

        self.__csp_search(self.__grid, 0, 0)

        if self.__timer:
            self.__t = time.time() - t_start

        return self.__solution

    def time(self):
        return self.__t


def main():

    grid = [list(map(int, input().split())) for i in range(9)]

    sudoku = Sudoku(grid, timer=True)

    result = sudoku.solve_as_sat()

    if result:
        for row in result:
            for i in range(len(row)):
                if i != len(row) - 1:
                    print(row[i], end=' ')
                else:
                    print(row[i], end='')
            print()
    else:
        print("The sudoku has no solution.")


if __name__ == "__main__":
    main()
