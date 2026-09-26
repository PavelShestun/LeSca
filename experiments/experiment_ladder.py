import numpy as np

def transfer_matrix_ladder(K_par, K_perp):
    """Строит точную трансфер-матрицу 4x4 для лестницы 2xN."""
    T = np.zeros((4, 4))
    # 4 состояния среза из двух спинов: (++, --, +-, -+)
    states = [(1, 1), (-1, -1), (1, -1), (-1, 1)]
    for i, (s1, s2) in enumerate(states):
        for j, (t1, t2) in enumerate(states):
            # Продольные связи: K_par * (s1*t1 + s2*t2)
            # Поперечные связи: 0.5 * K_perp * (s1*s2 + t1*t2)
            E = K_par * (s1*t1 + s2*t2) + 0.5 * K_perp * (s1*s2 + t1*t2)
            T[i, j] = np.exp(E)
    return T

def test_scaling_gap(K_par=1.0, K_perp=0.5, N_max=30):
    T = transfer_matrix_ladder(K_par, K_perp)
    eigvals = np.sort(np.linalg.eigvals(T))[::-1]
    l1, l2, l3, l4 = eigvals
    
    f_infty = np.log(l1)
    print("=" * 65)
    print(f"ПАРАМЕТРЫ: K_|| = {K_par}, K_⟂ = {K_perp}")
    print(f"Спектр 4x4: λ1={l1:.5f}, λ2={l2:.5f}, λ3={l3:.5f}, λ4={l4:.5f}")
    print(f"Спектральная щель Δ = 1 - λ2/λ1 = {1 - l2/l1:.5f}")
    print("=" * 65)
    
    results = []
    for N in range(2, N_max + 1, 2):
        Z_N = np.sum(eigvals**N)
        f_N = (1.0 / N) * np.log(Z_N)
        diff = f_N - f_infty
        
        # Теоретическая неасимптотическая верхняя граница
        bound = (1.0 / N) * ((l2/l1)**N + (l3/l1)**N + (l4/l1)**N)
        ratio = diff / bound if bound > 0 else 0
        results.append((N, diff, bound, ratio))
        
    print(f"{'N':>3} | {'f_N - f_inf':>15} | {'Теор. граница':>15} | {'Отношение (<= 1.0)':>20}")
    print("-" * 65)
    for N, diff, bound, ratio in results[:12]:
        print(f"{N:3d} | {diff:15.8e} | {bound:15.8e} | {ratio:20.6f}")
        assert diff <= bound + 1e-12, f"Контрпример найден при N={N}!"
        
    print("\n[УСПЕХ] Все неасимптотические границы строго подтверждены!")

if __name__ == "__main__":
    test_scaling_gap(K_par=0.8, K_perp=1.2, N_max=24)
