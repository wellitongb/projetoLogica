package cpu;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.logging.Level;
import java.util.logging.Logger;

import cpu.AlgorithmFCFS;
import cpu.Processo;

public abstract class Algorithm {
	//@ public model instance CriarLog1 Clog1;
	//@ public model instance CriarLog2 Clog2;
	//@ public model instance CriarLog3 Clog3;
	
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
    
    /*@ public invariant memoryProcess != null && memoryProcess.size() >= 0
    @ && (\forall int i;
    @ i >= 0 && i < memoryProcess.size();
    @ memoryProcess.get(i) != null);
    @*/
    
    /*@ public invariant FilaEstadoPronto != null && FilaEstadoPronto.size() >= 0
    @ && (\forall int i;
    @ i >= 0 && i < FilaEstadoPronto.size();
    @ FilaEstadoPronto.get(i) != null);
    @*/
    
    /*@ public invariant FilaEstadoFinalizado != null && FilaEstadoFinalizado.size() >= 0
    @ && (\forall int i;
    @ i >= 0 && i < FilaEstadoFinalizado.size();
    @ FilaEstadoFinalizado.get(i) != null);
    @*/
    
    /*@ public invariant FilaEstadoEspera != null && FilaEstadoEspera.size() >= 0
    @ && (\forall int i;
    @ i >= 0 && i < FilaEstadoEspera.size();
    @ FilaEstadoEspera.get(i) != null);
    @*/
    
    /*@ public invariant FilaEstadoNovo != null && FilaEstadoNovo.size() >= 0
    @ && (\forall int i;
    @ i >= 0 && i < FilaEstadoNovo.size();
    @ FilaEstadoNovo.get(i) != null);
    @*/
    
    protected /*@ spec_public nullable @*/ Processo ProcessoEstadoExecutando;
    
    //@ public invariant ProcessoEstadoExecutando != null || ProcessoEstadoExecutando == null;
    
    protected /*@ spec_public @*/ int nProcessos = 0, nProcessosNovos = 0, nProcessosNoSistema = 0;
    
    //@ public invariant 0 <= nProcessos;
    //@ public invariant 0 <= nProcessosNovos;
    //@ public invariant 0 <= nProcessosNoSistema;
    
    /**
     * Metodo construtor da classe Algorithm.
     * @param pathFile Representa o caminho do arquivo .dat a ser lido.
     */
    /*@ 	public normal_behavior
     @ 			requires pathFile != null;
     @ 			assignable this.FilaEstadoNovo;
     @ 			assignable this.FilaEstadoPronto;
     @ 			assignable this.FilaEstadoEspera;
     @ 			assignable this.FilaEstadoFinalizado;
     @ 			assignable this.memoryProcess;
     @ 			ensures this.FilaEstadoNovo != null;
     @ 			ensures this.FilaEstadoPronto != null;
     @ 			ensures this.FilaEstadoEspera != null;
     @ 			ensures this.FilaEstadoFinalizado != null;
     @ 			ensures this.memoryProcess != null && 
     @			(\forall int i; 0 <= i && i < memoryProcess.size(); memoryProcess.get(i) != null);
     @			ensures this.nProcessos == this.memoryProcess.size();
     @	also
     @		public exceptional_behavior
     @			requires pathFile == null;
     @			assignable \nothing;
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
    
    /*@ requires this.FilaEstadoNovo != null && this.nProcessosNovos <= this.nProcessos;
    @	assignable \nothing; 
    @*/
    protected abstract void novo();
    
    /*@ requires this.FilaEstadoEspera != null;
   	@	assignable \nothing;
    @*/
    protected abstract void espera();
    
    /*@ requires this.FilaEstadoPronto != null;
   	@	assignable \nothing;
    @*/
    protected abstract void executar();
    
    /*@ requires this.FilaEstadoNovo != null && this.FilaEstadoFinalizado != null && this.FilaEstadoEspera != null && this.FilaEstadoPronto != null && this.ProcessoEstadoExecutando != null;
    @	assignable \nothing;			
    @*/
    protected abstract void pronto();
    
    /*@	requires this.FilaEstadoFinalizado != null && this.ProcessoEstadoExecutando != null;
    @	assignable \nothing;
    @*/
    protected abstract void finalizado();
    
    /*@	requires Clog2 != null && Clog3 != null;
    @	assignable \nothing;
    @*/
    public abstract void run();
    
    /*@ requires Clog1 != null && Clog2 != null && Clog3 != null;
    @ assignable \nothing;
    @*/
    public /*@ pure @*/ abstract void close();
}
