package cpu;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.logging.Level;
import java.util.logging.Logger;

public abstract class Algorithm {
    protected /*@ spec_public nullable @*/ int executionTime = 0,timeSystem = 0, executionTimeTotal = 0;
    //@ public invariant 0 <= executionTime; 
	//@ public invariant 0 <= timeSystem;
	//@ public invariant 0 <= executionTimeTotal;
    
    protected /*@ spec_public nullable @*/ ArrayList<Processo> memoryProcess,FilaEstadoPronto,FilaEstadoFinalizado, FilaEstadoEspera, FilaEstadoNovo;
    //@ public invariant 0 <= memoryProcess.size();
    //@ public invariant 0 <= FilaEstadoPronto.size();
    //@ public invariant 0 <= FilaEstadoFinalizado.size();
    //@ public invariant 0 <= FilaEstadoEspera.size();
    //@ public invariant 0 <= FilaEstadoNovo.size();
    
    /*@ public invariant memoryProcess != null
    @ && (\forall int i;
    @ i >= 0 && i < memoryProcess.size();
    @ memoryProcess.get(i) != null);
    @*/
    
    /*@ public invariant FilaEstadoPronto != null
    @ && (\forall int i;
    @ i >= 0 && i < FilaEstadoPronto.size();
    @ FilaEstadoPronto.get(i) != null);
    @*/
    
    /*@ public invariant FilaEstadoFinalizado != null
    @ && (\forall int i;
    @ i >= 0 && i < FilaEstadoFinalizado.size();
    @ FilaEstadoFinalizado.get(i) != null);
    @*/
    
    /*@ public invariant FilaEstadoEspera != null
    @ && (\forall int i;
    @ i >= 0 && i < FilaEstadoEspera.size();
    @ FilaEstadoEspera.get(i) != null);
    @*/
    
    /*@ public invariant FilaEstadoNovo != null
    @ && (\forall int i;
    @ i >= 0 && i < FilaEstadoNovo.size();
    @ FilaEstadoNovo.get(i) != null);
    @*/
    
    protected /*@ spec_public nullable @*/ Processo ProcessoEstadoExecutando;
    
    protected /*@ spec_public @*/ int nProcessos = 0, nProcessosNovos = 0, nProcessosNoSistema = 0;
    
    //@ public invariant 0 <= nProcessos;
    //@ public invariant 0 <= nProcessosNovos;
    //@ public invariant 0 <= nProcessosNoSistema;
    
    /**
     * Método construtor da classe Algorithm.
     * @param pathFile Representa o caminho do arquivo .dat a ser lido.
     */
    /*@ public normal_behavior
     @ requires pathFile != null;
     @ assignable this.FilaEstadoNovo;
     @ assignable this.FilaEstadoPronto;
     @ assignable this.FilaEstadoEspera;
     @ assignable this.FilaEstadoFinalizado;
     @ assignable this.memoryProcess;
     @ ensures this.FilaEstadoNovo != null;
     @ ensures this.FilaEstadoPronto != null;
     @ ensures this.FilaEstadoEspera != null;
     @ ensures this.FilaEstadoFinalizado != null;
     @ ensures this.memoryProcess != null && 
     @		(\forall int i; 0 <= i && i < memoryProcess.size(); memoryProcess.get(i) != null);
     @ ensures this.nProcessos == this.memoryProcess.size();
     @*/
    public Algorithm(String pathFile){
        this.FilaEstadoNovo = new ArrayList<>();
        this.FilaEstadoPronto = new ArrayList<>();
        this.FilaEstadoEspera = new ArrayList<>();
        this.FilaEstadoFinalizado = new ArrayList<>();
        this.memoryProcess = new ArrayList<>();
        Scanner input;
        try {
            input = new Scanner(new FileReader(new File(pathFile)));
            Processo auxProcess;
            while(input.hasNextInt()){
                auxProcess = new Processo(input.nextInt(),input.nextInt() ,input.nextInt());
                for(int j = 0; j < auxProcess.getNPicos(); j++){
                    auxProcess.setPico(j, input.nextInt());
                }
                memoryProcess.add(auxProcess);
                nProcessos++;
            }
        }
        catch (FileNotFoundException ex) {
            Logger.getLogger(AlgorithmFCFS.class.getName()).log(Level.SEVERE, null, ex);
            System.out.println("Erro ao ler arquivo");
        } 
    }
    
    protected abstract void novo();
    
    protected abstract void espera();
    
    protected abstract void executar();
    
    protected abstract void pronto();
    
    protected abstract void finalizado();
    
    public abstract void run();
    
    public abstract void close();
}
